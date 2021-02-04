--  Module implementing a map from String to Positive as a trie

package Trie_List with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Trie is private;

   ---------------------------------
   -- Specification only entities --
   ---------------------------------

   function Holds_No_Memory (T : Trie) return Boolean with Ghost;
   --  Return True if all memory held by T has been deallocated

   subtype String_1 is String with
     Ghost,
     Predicate => String_1'First = 1 and String_1'Last >= 0;

   type String_Access is not null access String_1 with Ghost;
   W : String_Access := new String_1'("") with Ghost;
   --  Ghost variable standing for a universally quantified value in the
   --  postconditions of Insert and Erase.

   ------------------------------
   -- Functionalities of Tries --
   ------------------------------

   procedure Erase (T : in out Trie) with
     Post => Find (T, W.all) = 0 and Holds_No_Memory (T);

   function Find (T : Trie; K : String) return Natural with
     Annotate => (GNATprove, Terminating);

   procedure Insert (T : in out Trie; K : String; Value : Positive) with
     Pre  => Find (T, K) = 0,
     Post => Find (T, K) = Value
     and (if K /= W.all then Find (T, W.all) = Find (T, W.all)'Old);

private
   --  A trie is a tree where each node has a list of children, each
   --  associating a character to a trie. Its Value field will be 0 if the word
   --  is not in the map, or the associated value otherwise.

   type List_Cell;

   type List is access List_Cell;

   type Trie  is record
      Value    : Natural := 0;
      Children : List;
   end record;

   type List_Cell is record
      Key  : Character;
      Data : Trie;
      Next : List;
   end record;

   function Holds_No_Memory (T : Trie) return Boolean is (T.Children = null);
end Trie_List;
