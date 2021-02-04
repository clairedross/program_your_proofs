with Ada.Unchecked_Deallocation;

package body Trie_Array with SPARK_Mode is

   ----------------------
   -- Local Suprograms --
   ----------------------

   function At_End
     (X : access constant Trie_Cell) return access constant Trie_Cell
   is (X)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);
   --  At end borrow function to be able to express pledges on tries

   procedure Free_Cell is new Ada.Unchecked_Deallocation (Trie_Cell, Trie);

   procedure Lemma_Empty_Trie (T : not null access constant Trie_Cell) with
     Ghost,
     Pre => T.Value = 0 and (for all C in Character => T.Children (C) = null),
     Post => Model_Get (T, W.all, W'Last - W'Length) = 0;
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

   procedure Lemma_Same_Up_To_Last (S1 : String; S2 : String_1)
   with
     Ghost,
     Post =>
         (if S1 /= S2 then
            (S1'Length > 0 and then not Same_Up_To (S1, S2, S1'Last))
          or else S2'Length > S1'Length);
   --  Lemma: disjunction of cases linking Same_Up_To (S1, S2, S1'Last) to
   --    S1 /= S2.

   procedure Lemma_Unfold_Get
     (B : not null access constant Trie_Cell;
      I : Natural)
   with
     Ghost,
     Global => (Proof_In => W),
     Post =>
      (if W'Length = I then Model_Get (B, W.all, I) = B.Value)
     and
      (if W'Last > I
       then Model_Get (B, W.all, I)
         = Model_Get (B.Children (W (I + 1)), W.all, I + 1));
   --  Lemma: unfold the definition of Model_Get to help proof

   function Model_Get (T : Trie; K : String) return Natural with Ghost;
   --  Function representing the underlying map model of the trie. It returns
   --  0 if the key K is not associated to any value in the trie and the
   --  associated valie otherwise.

   function Model_Get (T   : access constant Trie_Cell;
                       K   : String;
                       Fst : Integer) return Natural
   is
     (if T = null then 0
      elsif Fst = K'Last then T.Value
      else Model_Get (T.Children (K (Fst + 1)), K, Fst + 1))
   with Subprogram_Variant => (Increases => Fst),
       Pre => Fst = K'Last
       or (K'Length > 0 and then Fst in K'First - 1 .. K'Last);
   --  Annex model function giving the value associated to the suffix of
   --  a string K starting from Fst in a trie T.

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

   procedure Erase (T : in out Trie) is
   begin
      if T = null then
         return;
      end if;

      for C in Character loop
         Erase (T.Children (C));
         pragma Loop_Invariant
           (for all D in Character'First .. C => T.Children (D) = null);
      end loop;

      Free_Cell (T);
   end Erase;

   ----------
   -- Find --
   ----------

   function Find (T : Trie; K : String) return Natural  with
     Refined_Post => Find'Result = Model_Get (T, K)
   is
   begin
      if T = null then
         pragma Assert (Model_Get (T, K) = 0);
         return 0;
      end if;

      declare
         O : access constant Trie_Cell := T;
      begin
         for I in K'Range loop
            --  O is not null
            pragma Loop_Invariant (O /= null);
            --  The value associated to K in T is the value associated to the
            --  suffix of K from I in B.
            pragma Loop_Invariant (Model_Get (T, K) = Model_Get (O, K, I - 1));

            O := O.Children (K (I));
            if O = null then
               pragma Assert (Model_Get (T, K) = 0);
               return 0;
            end if;
         end loop;
         pragma Assert (Model_Get (T, K) = O.Value);
         return O.Value;
      end;
   end Find;

   ------------
   -- Insert --
   ------------

   procedure Insert (T : in out Trie; K : String; Value : Positive) is
      Old_W : constant Natural := Model_Get (T, W.all, 0) with Ghost;
   begin
      if T = null then
         T := new Trie_Cell'(Children => (others => null), Value => 0);
         Lemma_Empty_Trie (T);
      end if;

      declare
         Fst : constant Integer := K'Last - K'Length with Ghost;
         B : not null access Trie_Cell := T;
      begin

         for I in K'Range loop
            if B.Children (K (I)) = null then
               B.Children (K (I)) :=
                 new Trie_Cell'(Children => (others => null), Value => 0);
               Lemma_Empty_Trie (B.Children (K (I)));
            end if;
            Lemma_Unfold_Get (B, I - K'First);
            Lemma_Unfold_Get (At_End (B), I - K'First);
            Lemma_Same_Up_To_Next (K, W.all, I);
            B := B.Children (K (I));

            --  If K and W share the same prefix up to I, then the value
            --  associated to the suffix of W in B is the value originaly
            --  associated to W in T.
            pragma Loop_Invariant
              (if Same_Up_To (K, W.all, I)
               then Old_W = Model_Get (B, W.all, I - K'First + 1));
            --  Pledges:
            --    * B cannot be null at the end of the borrow
            pragma Loop_Invariant (At_End (B) /= null);
            --    * The value associated to K in T at the end of the borrow
            --      will be the value associated to the suffix of K from I
            --      in B.
            pragma Loop_Invariant
              (Model_Get (At_End (T), K, Fst) = Model_Get (At_End (B), K, I));
            --    * If K and W share the same prefix up to I, then the value
            --      associated to W in T at the end of the borrow will be the
            --      value associated to its suffix in B.
            pragma Loop_Invariant
              (if Same_Up_To (K, W.all, I)
               then Model_Get (At_End (T), W.all, 0)
                 = Model_Get (At_End (B), W.all, I - K'First + 1));
            --    * Otherwise, the value associated to W in T at the end of the
            --      borrow will be the value originaly associated to W in T.
            pragma Loop_Invariant
              (if not Same_Up_To (K, W.all, I)
               then Model_Get (At_End (T), W.all, 0) = Old_W);
         end loop;
         B.Value := Value;
         Lemma_Same_Up_To_Last (K, W.all);
      end;
   end Insert;

   ----------------------
   -- Lemma_Empty_Trie --
   ----------------------

   procedure Lemma_Empty_Trie (T : not null access constant Trie_Cell) is null;

   ---------------------------
   -- Lemma_Same_Up_To_Next --
   ---------------------------

   procedure Lemma_Same_Up_To_Next (S1 : String; S2 : String_1; I : Positive)
   is null;

   ---------------------------
   -- Lemma_Same_Up_To_Last --
   ---------------------------

   procedure Lemma_Same_Up_To_Last (S1 : String; S2 : String_1) is null;

   ----------------------
   -- Lemma_Unfold_Get --
   ----------------------

   procedure Lemma_Unfold_Get
     (B : not null access constant Trie_Cell;
      I : Natural) is null;

   ---------------
   -- Model_Get --
   ---------------

   function Model_Get (T : Trie; K : String) return Natural is
     (Model_Get (T, K, K'Last - K'Length));

end Trie_Array;
