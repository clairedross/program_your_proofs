with Ada.Unchecked_Deallocation;

package body Trie_List with SPARK_Mode is

   ----------------------
   -- Local Suprograms --
   ----------------------

   function At_End
     (X : access constant List_Cell) return access constant List_Cell
   is (X)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);
   --  At end borrow function to be able to express pledges on tries

   procedure Free_Cell is new Ada.Unchecked_Deallocation (List_Cell, List);

   procedure Lemma_Empty_Trie (L : access constant List_Cell) with
     Ghost,
     Pre => L = null
     or else (L.Data.Value = 0 and L.Data.Children = null and L.Next = null),
     Post => (if W.all /= "" then Model_Get (L, W.all, 1) = 0);
   --  Model_Get returns 0 on every word on a empty trie

   procedure Lemma_Same_Up_To_Next (S1 : String; S2 : String_1; I : Positive)
   with
     Ghost,
     Pre  => I in S1'Range,
     Post =>
       (if Same_Up_To (S1, S2, I)
        then S2 (I - S1'First + 1) = S1 (I)
          and then (I = S1'First or else Same_Up_To (S1, S2, I - 1))
          and then S2'Last > I - S1'First
        else (I > S1'First and then not Same_Up_To (S1, S2, I - 1))
          or else (S2'Length = I - S1'First)
          or else (S2'Length > I - S1'First
             and then S2 (I - S1'First + 1) /= S1 (I)));
   --  Lemma: disjunction of cases linking Same_Up_To (S1, S2, I) to
   --    Same_Up_To (S1, S2, I - 1).

   procedure Lemma_Same_Up_To_Last (S1 : String; S2 : String_1; Seen : Boolean)
   with
     Ghost,
     Pre  => S1'Length > 0 and then
       (if not Seen and S2'Length /= 0 then S1'Length <= S2'Length
          and (S1'Length = 1 or else Same_Up_To (S1, S2, S1'Last - 1))),
     Post =>
         (if S1 /= S2 then S2'Length = 0
          or else Seen
          or else S1 (S1'Last) /= S2 (S1'Length)
          or else S1'Length /= S2'Length);
   --  Lemma: disjunction of cases linking Same_Up_To (S1, S2, S1'Last) to
   --    S1 /= S2.

   procedure Lemma_Unfold_Get (L : access constant List_Cell; I : Positive) with
     Ghost,
     Global => (Proof_In => W),
     Post =>
       (if I > W'Length then True
        elsif L = null then Model_Get (L, W.all, I) = 0
        elsif W (I) /= L.Key then Model_Get (L, W.all, I) = Model_Get (L.Next, W.all, I)
        elsif W'Length = I then Model_Get (L, W.all, I) = L.Data.Value
        else Model_Get (L, W.all, I) = Model_Get (L.Data.Children, W.all, I + 1));
   --  Lemma: unfold the definition of Model_Get to help proof

   function Model_Get (T : Trie; K : String) return Natural with Ghost;
   --  Function representing the underlying map model of the trie. It returns
   --  0 if the key K is not associated to any value in the trie and the
   --  associated valie otherwise.

   function Model_Get (L   : access constant List_Cell;
                       K   : String;
                       Fst : Integer) return Natural
   with Annotate => (GNATprove, Terminating),
       Pre => Fst in K'Range;
   --  Annex model function giving the value associated to the suffix of
   --  a string K starting from Fst in a List L.

   function Same_Up_To (S1, S2 : String; I : Positive) return Boolean is
     (S2'Length > I - S1'First
      and then
        (for all K in S1'First .. I => S1 (K) = S2 (K - S1'First + S2'First)))
   with Ghost,
       Pre => I in S1'Range;
   --  True if S1 and S2 have the vame prefix up to index I in S1

   -----------
   -- Erase --
   -----------

   procedure Erase (L : in out List) with
     Post => L = null
   is
   begin
      if L = null then
         return;
      end if;

      Erase (L.Data.Children);
      Erase (L.Next);
      Free_Cell (L);
   end Erase;

   procedure Erase (T : in out Trie) is
   begin
      Erase (T.Children);
      T.Value := 0;
   end Erase;

   ----------
   -- Find --
   ----------

   function Find (T : Trie; K : String) return Natural  with
     Refined_Post => Find'Result = Model_Get (T, K)
   is
      O : access constant List_Cell := T.Children;
   begin
      if K'Length = 0 then
         return T.Value;
      end if;

      for I in K'Range loop
         pragma Loop_Invariant (Model_Get (T, K) = Model_Get (O, K, I));
         while O /= null loop
            if O.Key = K (I) then
               exit;
            end if;
            O := O.Next;
            pragma Loop_Invariant (Model_Get (T, K) = Model_Get (O, K, I));
         end loop;

         if O = null then
            return 0;
         elsif I /= K'Last then
            O := O.Data.Children;
         end if;
      end loop;
      return O.Data.Value;
   end Find;

   ------------
   -- Insert --
   ------------

   procedure Insert (T : in out Trie; K : String; Value : Positive) is
      Old_W : constant Natural := Model_Get (T, W.all) with Ghost;
   begin
      if K'Length = 0 then
         T.Value := Value;
         return;
      elsif T.Children = null then
         T.Children := new List_Cell'(Key  => K (K'First),
                                      Data => (Value => 0, Children => null),
                                      Next => null);
         Lemma_Empty_Trie (T.Children);
      end if;

      declare
         B    : not null access List_Cell := T.Children;
         Seen : Boolean := False with Ghost;
         --  True if the value associated to W in T as been frozen by the
         --  borrow (ie. it is not accessible through B anymore).

      begin
         for I in K'Range loop
            --  If K and W share the same prefix up to I - 1, then the value
            --  associated to the suffix of W in B is the value originaly
            --  associated to W in T.
            pragma Loop_Invariant
              (if (I = K'First or else Same_Up_To (K, W.all, I - 1))
                 and I - K'First < W'Length
               then Old_W = Model_Get (B, W.all, I - K'First + 1));
            --  Pledges:
            --    * B cannot be null at the end of the borrow
            pragma Loop_Invariant (At_End (B) /= null);
            --    * The value associated to K in T at the end of the borrow
            --      will be the value associated to the suffix of K from I
            --      in B.
            pragma Loop_Invariant
              (Model_Get (At_End (T.Children), K, K'First)
               = Model_Get (At_End (B), K, I));
            --    * If K and W share the same prefix up to I - 1, then the
            --      value associated to W in T at the end of the borrow will be
            --      the value associated to its suffix in B.
            pragma Loop_Invariant
              (if (I = K'First or else Same_Up_To (K, W.all, I - 1))
                 and I - K'First < W'Length
               then Model_Get (At_End (T.Children), W.all, 1)
                 = Model_Get (At_End (B), W.all, I - K'First + 1));
            --    * Otherwise, the value associated to W in T at the end of the
            --      borrow will be the value originaly associated to W in T.
            pragma Loop_Invariant
              (if ((I /= K'First and then not Same_Up_To (K, W.all, I - 1))
                 or else I - K'First = W'Length)
                 and then W'Length > 0
               then Model_Get (At_End (T.Children), W.all, 1) = Old_W);

            --  Initialize Seen to True if W should not be searched in B,
            --  namely, if W and K do not share the same prefix up to I - 1 or
            --  if W is too short.
            Seen := ((I /= K'First and then not Same_Up_To (K, W.all, I - 1))
                 or else I - K'First = W'Length);

            loop
               Lemma_Unfold_Get (B, I - K'First + 1);
               Lemma_Unfold_Get (At_End (B), I - K'First + 1);
               Lemma_Same_Up_To_Next (K, W.all, I);

               --  Set Seen to true if the key of I corresponds to the current
               --  element of W, and we are not returning this element.
               Seen := Seen
                 or else (B.Key /= K (I) and W (I - K'First + 1) = B.Key);

               if B.Key = K (I) then
                  exit;
               elsif B.Next = null then
                  B.Next := new List_Cell'
                    (Key  => K (I),
                     Data => (Value => 0, Children => null),
                     Next => null);
                  B := B.Next;
                  Lemma_Empty_Trie (B);
                  exit;
               end if;
               B := B.Next;

               --  If Seen is True at loop entry, Seen will stay true. If Seen
               --  is True, W and K cannot have the same prefix up to I.
               pragma Loop_Invariant
                 (if Seen then not Same_Up_To (K, W.all, I)
                  else not Seen'Loop_Entry);
               --  If the value associated to W in T is accessible through B,
               --  it is the value originally associated to W in T.
               pragma Loop_Invariant
                 (if not Seen and then W'Length > 0
                  then Old_W = Model_Get (B, W.all, I - K'First + 1));
               --  Pledges:
               --    * B cannot be null at the end of the borrow
               pragma Loop_Invariant (At_End (B) /= null);
               --    * The value associated to K in T at the end of the borrow
               --      will be the value associated to the suffix of K from I
               --      in B.
               pragma Loop_Invariant
                 (Model_Get (At_End (T.Children), K, K'First)
                  = Model_Get (At_End (B), K, I));
               --    * If the value associated to W in T is accessible through
               --      B, its value at the end of the borrow will be the value
               --      associated to the suffix of W from I in B.
               pragma Loop_Invariant
                 (if not Seen and then W'Length > 0
                  then Model_Get (At_End (T.Children), W.all, 1)
                  = Model_Get (At_End (B), W.all, I - K'First + 1));
               --    * If the value associated to W in T is accessible through
               --      B, the value associated to W in T at the end of the
               --      borrow will be the value originaly associated to W in T.
               pragma Loop_Invariant
                 (if Seen and then W'Length > 0
                  then Model_Get (At_End (T.Children), W.all, 1) = Old_W);
            end loop;

            if I /= K'Last then
               B := B.Data.Children;
            end if;
         end loop;

         Lemma_Same_Up_To_Last (K, W.all, Seen);
         B.Data.Value := Value;
      end;
   end Insert;

   ----------------------
   -- Lemma_Empty_Trie --
   ----------------------

   procedure Lemma_Empty_Trie (L : access constant List_Cell) is null;

   ---------------------------
   -- Lemma_Same_Up_To_Next --
   ---------------------------

   procedure Lemma_Same_Up_To_Next (S1 : String; S2 : String_1; I : Positive)
   is null;

   ---------------------------
   -- Lemma_Same_Up_To_Last --
   ---------------------------

   procedure Lemma_Same_Up_To_Last (S1 : String; S2 : String_1; Seen : Boolean) is null;

   ----------------------
   -- Lemma_Unfold_Get --
   ----------------------

   procedure Lemma_Unfold_Get (L : access constant List_Cell; I : Positive) is null;

   ---------------
   -- Model_Get --
   ---------------

   function Model_Get (T : Trie; K : String) return Natural is
     (if K'Length = 0 then T.Value
      else Model_Get (T.Children, K, K'First));

   function Model_Get (L   : access constant List_Cell;
                       K   : String;
                       Fst : Integer) return Natural
   is
     (if L = null then 0
      elsif L.Key = K (Fst) then
          (if Fst = K'Last then L.Data.Value
           else Model_Get (L.Data.Children, K, Fst + 1))
      else Model_Get (L.Next, K, Fst));

end Trie_List;
