// Noa Leron 207131871
// Tsuri Farhana 315016907




/*
Following SPARK's
    https://github.com/AdaCore/spark2014/blob/master/testsuite/gnatprove/tests/red_black_trees/tree_model.ads
    https://github.com/AdaCore/spark2014/blob/master/testsuite/gnatprove/tests/red_black_trees/binary_trees.ads
    https://github.com/AdaCore/spark2014/blob/master/testsuite/gnatprove/tests/red_black_trees/binary_trees.adb

Which has acted as the basic data structure for the implementation of binary-search trees and in particular
balanced BSTs: red-black trees. In case you're interested in that original context, you're welcome to have a look
at the original paper, presented at NASA Formal Methods symposium 2017 by AdaCore's Claire Dross and Yannick Moy:

https://blog.adacore.com/research-corner-auto-active-verification-in-spark
https://blog.adacore.com/uploads/Auto-Active-Proof-of-Red-Black-Trees-in-SPARK.pdf

*/

module Tree_Model {
    const Max: int := 100
    const Empty: int := -1
    type Index_Type = x: int | Empty < x < Max
    type Extended_Index_Type = x: int | Empty <= x < Max
    type Extended_Index_Type_With_Max = x: int | Empty < x <= Max

    const All_Indexes := set I: Index_Type | true // meaning Empty < I < Max

    lemma Max_Indexes()
        ensures |All_Indexes| == Max
    {
        var I := 0;
        var Smaller, Larger := {}, All_Indexes;
        while I < Max
            invariant I <= Max
            invariant Smaller == set x | x in All_Indexes && 0 <= x < I
            invariant Larger == set x | x in All_Indexes && I <= x < Max
            invariant |Smaller| == I
            invariant Smaller + Larger == All_Indexes
            decreases Max - I
        {
            Smaller, Larger := Smaller + {I}, Larger - {I};
            I := I + 1;
        }
    }
    
    datatype Position_Type = Left | Right | Top
    type Direction = d: Position_Type | d != Top witness Left
    type D_Seq = q: seq<Direction> | |q| <= Max // sequence of directions modelling a path from the root of the tree to a node in the tree

    /*
        Type used to model the path from the root of a tree to a given node, which may or not be in the tree:
        - if a node is in the tree, the corresponding path will have K == true,
        and A will denote the path from the root to this node.
        - if a node is not in the tree, the corresponding path will have K == false and A will be empty.
    */
    datatype Path_Type = MaybePath(A: D_Seq, K: bool)

    ghost predicate Is_Concat(Q: D_Seq, V: D_Seq, P: D_Seq) { P == Q + V }

    // Type used to model the set of paths from the root of a tree to all nodes.
    // This is useful to reason about reachability properties over a tree.
    type Model_Type = q: seq<Path_Type> | |q| == Max witness *

    predicate Is_Add(S1: D_Seq, D: Direction, S2: D_Seq) { S2 == S1 + [D] }

    type Value_Set = set<nat>
}

// end of definitions from tree_model.ads, start of definitions from binary_trees.ads

/*
    Here's an implementation of binary trees, modeled using indexes inside an array.
    To avoid multiple copies, related trees are stored together forming a forest.
*/
module Binary_Trees {
    import opened Tree_Model

    type Cell = (Extended_Index_Type, Extended_Index_Type, Extended_Index_Type, Position_Type)
    function{:verify false} Left_Child(C: Cell): Extended_Index_Type { C.0 }
    function{:verify false} Right_Child(C: Cell): Extended_Index_Type { C.1 }
    function{:verify false} Parent(C: Cell): Extended_Index_Type { C.2 }
    function{:verify false} Position(C: Cell): Position_Type { C.3 }

    type Cell_Array = a: array<Cell> | a.Length == Max witness *
    
    // Component S gives the size of the forest. Only the cells up to index S belong to the forest. Cells after index S are free.
    type Forest = (Extended_Index_Type_With_Max, Cell_Array)
    function S(F: Forest): Extended_Index_Type_With_Max { F.0 }
    function C(F: Forest): Cell_Array { F.1 }

    ghost predicate Tree_Structure(F: Forest)
        reads C(F)
    {
        // Cells that are not allocated yet have default values
        (forall I: Index_Type :: S(F) < I < Max ==> C(F)[I] == (Empty, Empty, Empty, Top)) &&
        
        // Parent and children of all cells are allocated or empty
        (forall I: Index_Type :: Empty <= Parent(C(F)[I]) < S(F)) && 
        (forall I: Index_Type :: Empty <= Left_Child(C(F)[I]) < S(F)) && 
        (forall I: Index_Type :: Empty <= Right_Child(C(F)[I]) < S(F)) &&
        
        // If a cell is the root of a tree (position Top) it has no parent
        (forall I: Index_Type :: Position(C(F)[I]) == Top ==> Parent(C(F)[I]) == Empty) && 

        // If a cell I has a left child, then its left child has position Left and parent I
        (forall I: Index_Type :: Left_Child(C(F)[I]) != Empty ==> 
            Position(C(F)[Left_Child(C(F)[I])]) == Left && Parent(C(F)[Left_Child(C(F)[I])]) == I) &&

        // If a cell I has a right child, then its right child has position Right and parent I
        (forall I: Index_Type :: Right_Child(C(F)[I]) != Empty ==>
            Position(C(F)[Right_Child(C(F)[I])]) == Left && Parent(C(F)[Right_Child(C(F)[I])]) == I) &&
        
        // If a cell is a child (position Left or Right), then it is the child of its parent
        (forall I: Index_Type :: Parent(C(F)[I]) != Empty && Position(C(F)[I]) == Left ==> Left_Child(C(F)[Parent(C(F)[I])]) == I) &&
        (forall I: Index_Type :: Parent(C(F)[I]) != Empty && Position(C(F)[I]) == Right ==> Right_Child(C(F)[Parent(C(F)[I])]) == I)
    }

    ghost predicate Valid_Root(F: Forest, I: Index_Type)
        reads C(F)
    {
        I < S(F) && Position(C(F)[I]) == Top
    }

    ghost function Size(F: Forest): Extended_Index_Type_With_Max {
        S(F)
    }

    ghost function Parent_Of(F: Forest, I: Index_Type): Extended_Index_Type
        reads C(F)
    {
        Parent(C(F)[I])
    }

    ghost function Position_Of(F: Forest, I: Index_Type): Position_Type
        requires Tree_Structure(F)
        reads C(F)
    {
        Position(C(F)[I])
    }

    ghost function Peek(F: Forest, I: Index_Type, D: Direction): Extended_Index_Type
        reads C(F)
    {
        if D == Left then Left_Child(C(F)[I]) else Right_Child(C(F)[I])
    }

    ghost predicate In_Tree(F: Forest, Root: Index_Type, I: Index_Type)
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        reads C(F)
    {
        if I == Root then
            true
        else if I >= Size(F) then
            false
        else
            In_Tree_Rec(F, Root, Parent_Of(F, I), {I})
    }

    ghost predicate In_Tree_Rec(F: Forest, Root: Index_Type, I: Extended_Index_Type, Visited: set<Index_Type>)
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        reads C(F)
        decreases All_Indexes - Visited
    {
        if I == Root then
            true
        else if I == Empty || I in Visited then
            false
        else
            In_Tree_Rec(F, Root, Parent_Of(F, I), Visited + {I})
    }

    ghost function Path_From_Root(F: Forest, Root: Index_Type, I: Index_Type): D_Seq
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        requires In_Tree(F, Root, I)
        reads C(F)
    {
        Path_From_Root_Rec(F, Root, I, {})
    }

    // each node in the forest is a member of one rooted-tree:
    // the node is either the root of its own tree or its parent is a member of the same tree
    lemma {:verify false} Parent_In_Same_Tree(F: Forest, Root: Index_Type, I: Index_Type)
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        requires In_Tree(F, Root, I)
        ensures I == Root || In_Tree(F, Root, Parent_Of(F, I))
    {}

    lemma {:verify false} Lemma_Path_Length(F: Forest, Root: Index_Type, I: Index_Type, Visited: set<Index_Type>, Path: D_Seq)
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        requires In_Tree(F, Root, I)
        requires I !in Visited
        requires Visited < All_Indexes
        requires Path == Path_From_Root_Rec(F, Root, I, Visited)
        ensures |Path| < |All_Indexes - Visited|
        decreases All_Indexes - Visited
    {}
    
    ghost function Path_From_Root_Rec(F: Forest, Root: Index_Type, I: Index_Type, Visited: set<Index_Type>): D_Seq
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        requires In_Tree(F, Root, I)
        requires I !in Visited
        requires Visited < All_Indexes
        reads C(F)
        decreases All_Indexes - Visited
    {
        if I == Root then
            []
        else if Parent_Of(F, I) !in Visited then
            assert In_Tree(F, Root, Parent_Of(F, I)) by { Parent_In_Same_Tree(F, Root, I); }
            assert I in All_Indexes - Visited;
            var Path_To_Parent: D_Seq := Path_From_Root_Rec(F, Root, Parent_Of(F, I), Visited + {I});
            assert |Path_To_Parent| < |All_Indexes - (Visited + {I})| by {
                Lemma_Path_Length(F, Root, Parent_Of(F, I), Visited + {I}, Path_To_Parent);
            }
            assert |Path_To_Parent| + 1 < |All_Indexes - Visited| <= |All_Indexes| == Max by { Max_Indexes(); }
            assert Position_Of(F, I) == Left || Position_Of(F, I) == Right;
            var res := Path_To_Parent + [Position_Of(F, I)];
            assert |res| < |All_Indexes - Visited|;
            res
        else
            [] // should never reach here thanks to the tree having no cycles
    }

    lemma {:verify false} Lemma_Model_Length(F: Forest, Root: Index_Type, I: Index_Type, Model: seq<Path_Type>)
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        requires Model == Partial_Model_Rec(F, Root, Max - 1)
        ensures |Model| == Max
    {}

    /*
    The model of a tree in the forest is an array representing the path
    from the root leading to each node in the binary tree if any.
    */
    ghost function Model(F: Forest, Root: Index_Type): Model_Type
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        reads C(F)
    {
        var res := Partial_Model_Rec(F, Root, Max - 1);
        assert |res| == Max by { Lemma_Model_Length(F, Root, Max - 1, res); }
        res
    }

    ghost function Partial_Model_Rec(F: Forest, Root: Index_Type, I: Index_Type): seq<Path_Type>
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        reads C(F)
        decreases I
    {
        var Path_To_I :=
            if In_Tree(F, Root, I) then
                MaybePath(Path_From_Root(F, Root, I), true)
            else
                MaybePath([], false);
        if I == 0 then
            [Path_To_I]
        else
            Partial_Model_Rec(F, Root, I - 1) + [Path_To_I]
    } 




/*
    
    A method to extract the subtree starting at position D after I in the tree rooted at Root in a separate tree and store its root into V.

    Goal: Implement the method in Dafny, following (as closely as you can) the SPARK code (given below in a comment + reference to the original
    open-source online version), with the necessary modifications.

    Full verification is NOT expected in this case. Document the proof obligations for verification of this method using assertions and lemmas
    as we have learned, and try to prove correctness of some of the lammas (as much as you can).
    
    - As there are many not-too-trivial properties to consider, the main challenge in this exercise 
      is to try an understand the definitions, the properties, and the data structure, and then try to argue
      for the correctness of the code
    - Wherever Dafny takes too long to verify correctness ("timing out" after a short attempt), don't worry about it;
      instead, in such cases, feel free to try and document in words, shortly, for as many properties as you can,
      what makes them correct. A sign of success will be if you managed to write the expected code correctly
      and give me some convincing signs that you've managed to comprehend the details of the data structure
      along with its invariants (as defined in the Tree_Structure ghost predicate)
*/
    method Extract(F: Forest, Root: Index_Type, I: Index_Type, D: Direction, ghost F_Old: Forest) returns (V: Extended_Index_Type)
        requires Tree_Structure(F)
        requires Valid_Root(F, Root) && Model(F, Root)[I].K
        requires C(F) != C(F_Old) // the backup forest references ("points") to a different array, one that will NOT be modified
        requires C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old) // and it is indeed a backup of the given forest, holding equal contents on entry
        modifies C(F) // in contrast to C(F_Old) which is a different array (as mentioned above)
        ensures Tree_Structure(F)
        // Root is still the root of a tree
        ensures Valid_Root(F, Root)
        // V was the child D of I, which is now Empty
        ensures V == Peek(F_Old, I, D) && Peek(F, I, D) == Empty
        // Except for V, the value of parent link is preserved
        ensures forall J: Index_Type :: J != V ==> Parent_Of(F, J) == Parent_Of(F_Old, J)
        // Except for V, the value of position is preserved for nodes which have a parent
        ensures forall J: Index_Type :: J != V && Parent_Of(F, J) != Empty ==> Position_Of(F, J) == Position_Of(F_Old, J)
        // Except at I for child D, all other children are preserved
        ensures forall J: Index_Type, E: Direction :: J != I || E != D ==> Peek(F, J, E) == Peek(F_Old, J, E)
        // Except for I and V (which was not a root node anyway), all root nodes are preserved
        ensures forall T: Index_Type :: Valid_Root(F_Old, T) && I != T && V != T ==> Valid_Root(F, T);
        // All other trees in the forest are preserved
        ensures forall T: Index_Type :: Valid_Root(F_Old, T) && Root != T && V != T ==> Model(F, T) == Model(F_Old, T)
        // V is either Empty or a new root
        ensures V != Empty ==> Valid_Root(F, V)
        // Nodes previously in the tree rooted at Root either remain nodes in
        // the tree rooted at Root, or for those nodes which have V on their
        // path, become nodes in the tree rooted at V
        ensures forall I: Index_Type :: Model(F_Old, Root)[I].K ==>
            if V != Empty && Model(F_Old, Root)[V].A <= Model(F_Old, Root)[I].A then Model(F, V)[I].K else Model(F, Root)[I].K
        // Nodes in the tree rooted at Root were previously in the tree rooted at Root
        ensures forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F_Old, Root)[I].K
        // Nodes in the tree rooted at V were previously in the tree rooted at Root
        ensures forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> Model(F_Old, Root)[I].K
        // Paths are preserved for nodes in the tree rooted at Root
        ensures forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F, Root)[I].A == Model(F_Old, Root)[I].A
        // The path for nodes in the tree rooted at V is obtained by subtracting
        // the path from Root to V from the path from Root to the node
        ensures forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> 
            Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[I].A, Model(F_Old, Root)[I].A)
    {
        // pre condition:
        assert Tree_Structure(F);
        assert Valid_Root(F, Root) && Model(F, Root)[I].K;
        assert C(F) != C(F_Old);
        assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);

		V := (if D == Left then Left_Child(C(F)[I]) else Right_Child(C(F)[I]));
        
        assert Tree_Structure(F); // from pre cond
        assert forall J: Index_Type :: Empty <= Left_Child(C(F)[J]) < S(F);
        assert Empty <= Left_Child(C(F)[I]) < S(F);
        assert D == Left ==> Empty <= V < S(F);
        assert forall J: Index_Type :: Empty <= Right_Child(C(F)[J]) < S(F);
        assert Empty <= Right_Child(C(F)[I]) < S(F);
        assert D == Right ==> Empty <= V < S(F);
        assert Empty <= V < S(F); // Since this statment is true when D == Left or D == right, and since Direction = {Left, Right}, this statment is always true

        // v is not a variable in the pre condition
        // pre condition:
        assert Tree_Structure(F);
        assert Valid_Root(F, Root) && Model(F, Root)[I].K;
        assert C(F) != C(F_Old);
        assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);

        // Lemma_eq_arrays_implies_eq_parents_children pre condition:
        assert Tree_Structure(F);
        assert  Tree_Structure(F_Old);
        assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);
        Lemma_eq_arrays_implies_eq_parents_children(F, F_Old);
        // Lemma_eq_arrays_implies_eq_parents_children post condition:
        assert forall J: Index_Type :: Parent_Of(F, J) == Parent_Of(F_Old, J);

        // Lemma_eq_arrays_implies_eq_positions pre condition
        assert Tree_Structure(F);
        assert  Tree_Structure(F_Old);
        assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);
        Lemma_eq_arrays_implies_eq_positions(F, F_Old);
        // Lemma_eq_arrays_implies_eq_positions post condition
        assert forall J: Index_Type :: Position_Of(F, J) == Position_Of(F_Old, J);

        // Lemma_eq_arrays_implies_eq_diractions pre condition:
        assert Tree_Structure(F);
        assert  Tree_Structure(F_Old);
        assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);
        Lemma_eq_arrays_implies_eq_diractions(F, F_Old);
        // Lemma_eq_arrays_implies_eq_diractions post condition:
        assert forall J: Index_Type, E: Direction :: (Peek(F, J, E) == Peek(F_Old, J, E));

		if V != Empty
		{
            // guard negation:
            assert V != Empty;

            // pre condition:
            assert Tree_Structure(F);
            assert Valid_Root(F, Root) && Model(F, Root)[I].K;
            assert C(F) != C(F_Old);
            assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);

            assert Empty <= V < S(F); // Proved earlier
            assert forall J: Index_Type :: Parent_Of(F, J) == Parent_Of(F_Old, J); // Proved earlier
            assert forall J: Index_Type :: Position_Of(F, J) == Position_Of(F_Old, J); // Proved earlier
            assert forall J: Index_Type, E: Direction :: (Peek(F, J, E) == Peek(F_Old, J, E)); // Proved earlier

            // Prove V != Root (since Root is a root, but V isn't)
            assert Parent(C(F)[V]) == I;
            assert Parent(C(F)[V]) != Empty;
            assert Position(C(F)[V]) != Top;
            assert Valid_Root(F, Root);
            assert Position(C(F)[Root]) == Top;
            assert C(F)[Root] != C(F)[V];
            assert V != Root;
            

			if D == Left
			{   
                // gaurd:
                assert D == Left;

                // pre condition:
                assert Tree_Structure(F);
                assert Valid_Root(F, Root) && Model(F, Root)[I].K; 
                assert C(F) != C(F_Old);
                assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);

                assert Empty <= V < S(F); // Proved earlier
                assert forall J: Index_Type :: Parent_Of(F, J) == Parent_Of(F_Old, J); // Proved earlier
                assert forall J: Index_Type :: Position_Of(F, J) == Position_Of(F_Old, J); // Proved earlier
                assert forall J: Index_Type, E: Direction :: (Peek(F, J, E) == Peek(F_Old, J, E)); // Proved earlier

                ghost var I_Old := (Left_Child(C(F)[I]), Right_Child(C(F)[I]), Parent(C(F)[I]), Position(C(F)[I]));
                assert (Parent_Of(F, V) == I);
                assert I_Old == (V, Right_Child(C(F)[I]), Parent(C(F)[I]), Position(C(F)[I]));
                
				C(F)[I] := (Empty, Right_Child(C(F)[I]), Parent(C(F)[I]), Position(C(F)[I]));
                assert (Parent_Of(F, V) == I); 
			    C(F)[V] := (Left_Child(C(F)[V]), Right_Child(C(F)[V]), Empty, Top);

            // prove Valid_Root(V)
                assert Empty <= V < S(F); // Proved earlier
                assert Position(C(F)[V]) == Top;
                assert Valid_Root(F, V);

            // Prove Model(F_Old, Root)[V].K 
                // assert Model(F, Root)[I].K;

                // Lemma_eq_arrays_implies_Tree_Structure pre condition:
                assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);
                assert Tree_Structure(F);
                Lemma_eq_arrays_implies_Tree_Structure(F, F_Old);
                // Lemma_eq_arrays_implies_Tree_Structure post condition:
                assert Tree_Structure(F_Old);

                // Lemma_eq_arrays_implies_eq_models pre condition:
                assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);
                assert Tree_Structure(F);
                assert Tree_Structure(F_Old);
                Lemma_eq_arrays_implies_eq_models(F, F_Old);
                // Lemma_eq_arrays_implies_eq_models post condition
                assert forall T: Index_Type :: Valid_Root(F, T) ==> Valid_Root(F_Old, T) && (Model(F, T) == Model(F_Old, T));

                assert Model(F, Root)[I].K;
                assert Model(F, Root)[I] == Model(F_Old, Root)[I];
                assert Model(F_Old, Root)[I].K;
                assert Parent(C(F)[V]) == I;

                // Lemma_Model_Parent_implies_Model_child pre condition:
                assert Tree_Structure(F);
                assert Valid_Root(F, Root);
                assert Model(F, Root)[I].K;
                assert V != Empty;
                assert Parent(C(F)[V]) == I;
                Lemma_Model_Parent_implies_Model_child(F, Root, I, D, V);
                // Lemma_Model_Parent_implies_Model_child post condition:
                assert Model(F_Old, Root)[V].K;


            // Prove forall J: Index_Type :: (J != V) ==> Parent_Of(F, J) == Parent_Of(F_Old, J):
                // Before the modification of F we showed:
                // forall J: Index_Type :: Parent_Of(F, J) == Parent_Of(F_Old, J),
                // Since then, V's parent was the only changed parent 
                assert forall J: Index_Type :: (J != V) ==> Parent_Of(F, J) == Parent_Of(F_Old, J);
            // Prove Tree_Structure(F):    
                // Lemma_Tree_Structure pre condition:
                assert V != Empty;
                assert Position(C(F)[V]) == Top;
                assert Parent(C(F)[V]) == Empty;
                assert D == Left ==> Left_Child(C(F)[I]) == Empty;
                assert D == Right ==> Right_Child(C(F)[I]) == Empty;
                assert forall J: Index_Type :: S(F) < J < Max ==> C(F)[J] == (Empty, Empty, Empty, Top);
                assert forall J: Index_Type :: J != V ==> Empty <= Parent(C(F)[J]) < S(F);
                assert forall J: Index_Type :: J != I ==> Empty <= Left_Child(C(F)[J]) < S(F) ;
                assert forall J: Index_Type :: J != I ==> Empty <= Right_Child(C(F)[J]) < S(F);
                assert if D == Left then Left_Child(C(F)[I]) == Empty else Empty <= Left_Child(C(F)[I]) < S(F);
                assert if D == Right then Right_Child(C(F)[I]) == Empty else Empty <= Right_Child(C(F)[I]) < S(F);
                assert forall J: Index_Type :: J != V  ==> (Position(C(F)[J]) == Top ==> Parent(C(F)[J]) == Empty);
                assert Position(C(F)[V]) == Top ==> Parent(C(F)[V]) == Empty;
                assert forall J: Index_Type :: J != I ==> (Left_Child(C(F)[J]) != Empty ==> 
                        Position(C(F)[Left_Child(C(F)[J])]) == Left && Parent(C(F)[Left_Child(C(F)[J])]) == J); // prove J's left child != V
                assert forall J: Index_Type :: J != I ==> (Right_Child(C(F)[J]) != Empty ==>
                        Position(C(F)[Right_Child(C(F)[J])]) == Left && Parent(C(F)[Right_Child(C(F)[J])]) == J); // prove J's right child != V
                assert if D == Left then Left_Child(C(F)[I]) == Empty else (Left_Child(C(F)[I]) != Empty ==> 
                        Position(C(F)[Left_Child(C(F)[I])]) == Left && Parent(C(F)[Left_Child(C(F)[I])]) == I); // prove I's left child != V)
                assert if D == Right then Right_Child(C(F)[I]) == Empty else (Right_Child(C(F)[I]) != Empty ==>
                        Position(C(F)[Right_Child(C(F)[I])]) == Right && Parent(C(F)[Right_Child(C(F)[I])]) == I); // prove I's right child != V)
                assert forall J: Index_Type :: Parent(C(F)[J]) != I  ==> (Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Left ==> Left_Child(C(F)[Parent(C(F)[J])]) == J);
                assert forall J: Index_Type :: Parent(C(F)[J]) != I ==> (Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Right ==> Right_Child(C(F)[Parent(C(F)[J])]) == J);
                assert forall J: Index_Type :: Parent(C(F)[J]) == I ==> (if J != V then (Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Left ==> Left_Child(C(F)[Parent(C(F)[J])]) == J) else Parent(C(F)[J]) == Empty);
                assert forall J: Index_Type :: Parent(C(F)[J]) == I ==> (if J != V then (Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Right ==> Right_Child(C(F)[Parent(C(F)[J])]) == J) else Parent(C(F)[J]) == Empty);

                Lemma_Tree_Structure(F, Root, I, D, V);

                // Lemma_Tree_Structure post condition:
                assert forall J: Index_Type :: S(F) < J < Max ==> C(F)[J] == (Empty, Empty, Empty, Top);
                assert forall J: Index_Type :: Empty <= Parent(C(F)[J]) < S(F);
                assert forall J: Index_Type :: Empty <= Left_Child(C(F)[J]) < S(F) ;
                assert forall J: Index_Type :: Empty <= Right_Child(C(F)[J]) < S(F);
                assert forall J: Index_Type :: Position(C(F)[J]) == Top ==> Parent(C(F)[J]) == Empty;
                assert forall J: Index_Type :: Left_Child(C(F)[J]) != Empty ==> 
                        Position(C(F)[Left_Child(C(F)[J])]) == Left && Parent(C(F)[Left_Child(C(F)[J])]) == J;
                assert forall J: Index_Type :: Right_Child(C(F)[J]) != Empty ==>
                        Position(C(F)[Right_Child(C(F)[J])]) == Right && Parent(C(F)[Right_Child(C(F)[J])]) == J;
                assert forall J: Index_Type :: Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Left ==> Left_Child(C(F)[Parent(C(F)[J])]) == J;
                assert forall J: Index_Type :: Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Right ==> Right_Child(C(F)[Parent(C(F)[J])]) == J;

                assert Tree_Structure(F);

            // Prove forall J: Index_Type :: (J != V) ==> Position_Of(F, J) == Position_Of(F_Old, J):
                // Before the modification of F we showed:
                // forall J: Index_Type :: Position_of(F, J) == Position_of(F_Old, J),
                // Since then, V's position was the only changed position
                assert forall J: Index_Type :: (J != V) ==> Position_Of(F, J) == Position_Of(F_Old, J);

            // Prove forall J: Index_Type, E: Direction :: (!Model(F_Old, Root)[J].K) ==> (Peek(F, J, E) == Peek(F_Old, J, E)):
                // Before the modification of F we showed:
                // forall J: Index_Type, E: Direction :: (Peek(F, J, E) == Peek(F_Old, J, E)),
                // Since then, I's left child was the only changed child, 
                // and since I is in the tree rooted in Root (in F_Old), 
                // every node that didn't belong to the tree rooted in Root in F_Old, has the same children in the same positions.
                assert forall J: Index_Type, E: Direction :: (!Model(F_Old, Root)[J].K) ==> (Peek(F, J, E) == Peek(F_Old, J, E));
                
            // prove_post_lemma pre condition:
                assert S(F) == S(F_Old); // The size of F didn't change
                assert Valid_Root(F_Old, Root); // F_Old didn't change
                assert V != Root;
                assert Valid_Root(F, V);
                assert Model(F_Old, Root)[V].K;
                assert forall J: Index_Type :: (J != V) ==> Parent_Of(F, J) == Parent_Of(F_Old, J);
                assert Tree_Structure(F);
                assert forall J: Index_Type :: (J != V) ==> Position_Of(F, J) == Position_Of(F_Old, J);
                assert forall J: Index_Type, E: Direction :: (!Model(F_Old, Root)[J].K) ==> (Peek(F, J, E) == Peek(F_Old, J, E));             
			}              
            else
			{
                // gaurd negation:
                assert D != Left;
                assert D == Right;

                // pre condition:
                assert Tree_Structure(F);
                assert Valid_Root(F, Root) && Model(F, Root)[I].K;
                assert C(F) != C(F_Old);
                assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);

                assert Empty <= V < S(F); // Proved earlier
                assert forall J: Index_Type :: Parent_Of(F, J) == Parent_Of(F_Old, J); // Proved earlier
                assert forall J: Index_Type :: Position_Of(F, J) == Position_Of(F_Old, J); // Proved earlier
                assert forall J: Index_Type, E: Direction :: (Peek(F, J, E) == Peek(F_Old, J, E)); // Proved earlier

				C(F)[I] := (Left_Child(C(F)[I]), Empty, Parent(C(F)[I]), Position(C(F)[I]));
                assert (Parent_Of(F, V) == I); 
			    C(F)[V] := (Left_Child(C(F)[V]), Right_Child(C(F)[V]), Empty, Top);

            // prove Valid_Root(V)
                assert Empty <= V < S(F); // Proved earlier
                assert Position(C(F)[V]) == Top;
                assert Valid_Root(F, V);

            // Prove Model(F_Old, Root)[V].K
                // assert Model(F, Root)[I].K;
                
                // Lemma_eq_arrays_implies_Tree_Structure pre condition:
                assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);
                assert Tree_Structure(F);
                Lemma_eq_arrays_implies_Tree_Structure(F, F_Old);
                // Lemma_eq_arrays_implies_Tree_Structure post condition:
                assert Tree_Structure(F_Old);

                // Lemma_eq_arrays_implies_eq_models pre condition:
                assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);
                assert Tree_Structure(F);
                assert Tree_Structure(F_Old);
                Lemma_eq_arrays_implies_eq_models(F, F_Old);
                // Lemma_eq_arrays_implies_eq_models post condition
                assert forall T: Index_Type :: Valid_Root(F, T) ==> Valid_Root(F_Old, T) && (Model(F, T) == Model(F_Old, T));

                assert Model(F, Root)[I].K;
                assert Model(F, Root)[I] == Model(F_Old, Root)[I];
                assert Model(F_Old, Root)[I].K;
                assert Parent(C(F)[V]) == I;

                // Lemma_Model_Parent_implies_Model_child pre condition:
                assert Tree_Structure(F);
                assert Valid_Root(F, Root);
                assert Model(F, Root)[I].K;
                assert V != Empty;
                assert Parent(C(F)[V]) == I;
                Lemma_Model_Parent_implies_Model_child(F, Root, I, D, V);
                // Lemma_Model_Parent_implies_Model_child post condition:
                assert Model(F, Root)[V].K;


            // Prove forall J: Index_Type :: (J != V) ==> Parent_Of(F, J) == Parent_Of(F_Old, J):
                // Before the modification of F we showed:
                // forall J: Index_Type :: Parent_Of(F, J) == Parent_Of(F_Old, J),
                // Since then, V's parent was the only changed parent 
                assert forall J: Index_Type :: (J != V) ==> Parent_Of(F, J) == Parent_Of(F_Old, J);
            // Prove Tree_Structure(F):    
                // Lemma_Tree_Structure pre condition:
                assert V != Empty;
                assert Position(C(F)[V]) == Top;
                assert Parent(C(F)[V]) == Empty;
                assert D == Left ==> Left_Child(C(F)[I]) == Empty;
                assert D == Right ==> Right_Child(C(F)[I]) == Empty;
                assert forall J: Index_Type :: S(F) < J < Max ==> C(F)[J] == (Empty, Empty, Empty, Top);
                assert forall J: Index_Type :: J != V ==> Empty <= Parent(C(F)[J]) < S(F);
                assert forall J: Index_Type :: J != I ==> Empty <= Left_Child(C(F)[J]) < S(F) ;
                assert forall J: Index_Type :: J != I ==> Empty <= Right_Child(C(F)[J]) < S(F);
                assert if D == Left then Left_Child(C(F)[I]) == Empty else Empty <= Left_Child(C(F)[I]) < S(F);
                assert if D == Right then Right_Child(C(F)[I]) == Empty else Empty <= Right_Child(C(F)[I]) < S(F);
                assert forall J: Index_Type :: J != V  ==> (Position(C(F)[J]) == Top ==> Parent(C(F)[J]) == Empty);
                assert Position(C(F)[V]) == Top ==> Parent(C(F)[V]) == Empty;
                assert forall J: Index_Type :: J != I ==> (Left_Child(C(F)[J]) != Empty ==> 
                        Position(C(F)[Left_Child(C(F)[J])]) == Left && Parent(C(F)[Left_Child(C(F)[J])]) == J); // prove J's left child != V
                assert forall J: Index_Type :: J != I ==> (Right_Child(C(F)[J]) != Empty ==>
                        Position(C(F)[Right_Child(C(F)[J])]) == Left && Parent(C(F)[Right_Child(C(F)[J])]) == J); // prove J's right child != V
                assert if D == Left then Left_Child(C(F)[I]) == Empty else (Left_Child(C(F)[I]) != Empty ==> 
                        Position(C(F)[Left_Child(C(F)[I])]) == Left && Parent(C(F)[Left_Child(C(F)[I])]) == I); // prove I's left child != V)
                assert if D == Right then Right_Child(C(F)[I]) == Empty else (Right_Child(C(F)[I]) != Empty ==>
                        Position(C(F)[Right_Child(C(F)[I])]) == Right && Parent(C(F)[Right_Child(C(F)[I])]) == I); // prove I's right child != V)
                assert forall J: Index_Type :: Parent(C(F)[J]) != I  ==> (Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Left ==> Left_Child(C(F)[Parent(C(F)[J])]) == J);
                assert forall J: Index_Type :: Parent(C(F)[J]) != I ==> (Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Right ==> Right_Child(C(F)[Parent(C(F)[J])]) == J);
                assert forall J: Index_Type :: Parent(C(F)[J]) == I ==> (if J != V then (Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Left ==> Left_Child(C(F)[Parent(C(F)[J])]) == J) else Parent(C(F)[J]) == Empty);
                assert forall J: Index_Type :: Parent(C(F)[J]) == I ==> (if J != V then (Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Right ==> Right_Child(C(F)[Parent(C(F)[J])]) == J) else Parent(C(F)[J]) == Empty);

                Lemma_Tree_Structure(F, Root, I, D, V);

                // Lemma_Tree_Structure post condition:
                assert forall J: Index_Type :: S(F) < J < Max ==> C(F)[J] == (Empty, Empty, Empty, Top);
                assert forall J: Index_Type :: Empty <= Parent(C(F)[J]) < S(F);
                assert forall J: Index_Type :: Empty <= Left_Child(C(F)[J]) < S(F) ;
                assert forall J: Index_Type :: Empty <= Right_Child(C(F)[J]) < S(F);
                assert forall J: Index_Type :: Position(C(F)[J]) == Top ==> Parent(C(F)[J]) == Empty;
                assert forall J: Index_Type :: Left_Child(C(F)[J]) != Empty ==> 
                        Position(C(F)[Left_Child(C(F)[J])]) == Left && Parent(C(F)[Left_Child(C(F)[J])]) == J;
                assert forall J: Index_Type :: Right_Child(C(F)[J]) != Empty ==>
                        Position(C(F)[Right_Child(C(F)[J])]) == Right && Parent(C(F)[Right_Child(C(F)[J])]) == J;
                assert forall J: Index_Type :: Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Left ==> Left_Child(C(F)[Parent(C(F)[J])]) == J;
                assert forall J: Index_Type :: Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Right ==> Right_Child(C(F)[Parent(C(F)[J])]) == J;

                assert Tree_Structure(F);

            // Prove forall J: Index_Type :: (J != V) ==> Position_Of(F, J) == Position_Of(F_Old, J):
                // Before the modification of F we showed:
                // forall J: Index_Type :: Position_of(F, J) == Position_of(F_Old, J),
                // Since then, V's position was the only changed position
                assert forall J: Index_Type :: (J != V) ==> Position_Of(F, J) == Position_Of(F_Old, J);

            // Prove forall J: Index_Type, E: Direction :: (!Model(F_Old, Root)[J].K) ==> (Peek(F, J, E) == Peek(F_Old, J, E)):
                // Before the modification of F we showed:
                // forall J: Index_Type, E: Direction :: (Peek(F, J, E) == Peek(F_Old, J, E)),
                // Since then, I's right child was the only changed child, 
                // and since I is in the tree rooted in Root (in F_Old), 
                // every node that didn't belong to the tree rooted in Root in F_Old, has the same children in the same positions.
                assert forall J: Index_Type, E: Direction :: (!Model(F_Old, Root)[J].K) ==> (Peek(F, J, E) == Peek(F_Old, J, E));

            //  prove_post_lemma pre condition:
                assert S(F) == S(F_Old);
                assert Valid_Root(F_Old, Root);
                assert V != Root;
                assert Valid_Root(F, V);
                assert Model(F_Old, Root)[V].K;
                assert forall I: Index_Type :: (I != V) ==> Parent_Of(F, I) == Parent_Of(F_Old, I);
                assert Tree_Structure(F);
                assert forall I: Index_Type :: (I != V) ==> Position_Of(F, I) == Position_Of(F_Old, I);
                assert forall J: Index_Type, E: Direction :: (!Model(F_Old, Root)[J].K) ==> (Peek(F, J, E) == Peek(F_Old, J, E));
			}
                    
            // Prove_Post pre condition:
            assert S(F) == S(F_Old);
            assert Valid_Root(F_Old, Root);
            assert V != Root;
            assert Valid_Root(F, V);
            assert Model(F_Old, Root)[V].K;
            assert forall I: Index_Type :: (I != V) ==> Parent_Of(F, I) == Parent_Of(F_Old, I);
            assert Tree_Structure(F);
            assert forall I: Index_Type :: (I != V) ==> Position_Of(F, I) == Position_Of(F_Old, I);
            assert forall J: Index_Type, E: Direction :: (!Model(F_Old, Root)[J].K) ==> (Peek(F, J, E) == Peek(F_Old, J, E));

            Prove_Post(F, Root, I, D, F_Old, V);

            // Prove_Post post condition:
            assert forall I: Index_Type :: Model(F_Old, Root)[I].K ==>
                if V != Empty && Model(F_Old, Root)[V].A <= Model(F_Old, Root)[I].A then Model(F, V)[I].K else Model(F, Root)[I].K;
            assert forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F_Old, Root)[I].K;
            assert forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> Model(F_Old, Root)[I].K;
            assert forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F, Root)[I].A == Model(F_Old, Root)[I].A;
            assert forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> 
                    Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[I].A, Model(F_Old, Root)[I].A);
            assert forall T: Index_Type :: Valid_Root(F_Old, T) && Root != T && V != T ==> Model(F, T) == Model(F_Old, T);

            // post condition:
            assert Tree_Structure(F);
            assert Valid_Root(F, Root);
            assert V == Peek(F_Old, I, D) && Peek(F, I, D) == Empty;
            assert forall J: Index_Type :: J != V ==> Parent_Of(F, J) == Parent_Of(F_Old, J);
            assert forall J: Index_Type :: J != V && Parent_Of(F, J) != Empty ==> Position_Of(F, J) == Position_Of(F_Old, J);
            assert forall J: Index_Type, E: Direction :: J != I || E != D ==> Peek(F, J, E) == Peek(F_Old, J, E);
            assert forall T: Index_Type :: Valid_Root(F_Old, T) && I != T && V != T ==> Valid_Root(F, T);
            assert forall T: Index_Type :: Valid_Root(F_Old, T) && Root != T && V != T ==> Model(F, T) == Model(F_Old, T);
            assert V != Empty ==> Valid_Root(F, V);
            assert forall I: Index_Type :: Model(F_Old, Root)[I].K ==>
                if V != Empty && Model(F_Old, Root)[V].A <= Model(F_Old, Root)[I].A then Model(F, V)[I].K else Model(F, Root)[I].K;
            assert forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F_Old, Root)[I].K;
            assert forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> Model(F_Old, Root)[I].K;
            assert forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F, Root)[I].A == Model(F_Old, Root)[I].A;
            assert forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> 
                Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[I].A, Model(F_Old, Root)[I].A);
		
		}

        else
        {
            // guard's negation:
            assert V == Empty;

            // pre condition:
            assert Tree_Structure(F);
            assert Valid_Root(F, Root) && Model(F, Root)[I].K;
            assert C(F) != C(F_Old);
            assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);

            // Showing V != Root, since V is Empty, but Root isn't
            assert V == Empty;
            assert Valid_Root(F, Root);
            assert Root != Empty;
            assert V != Root;

            // Extract_Empty pre condition:
            assert if D == Left then V == Left_Child(C(F)[I]) else V ==Right_Child(C(F)[I]);
            assert Tree_Structure(F);
            assert Valid_Root(F, Root) && Model(F, Root)[I].K;
            assert C(F) != C(F_Old);
            assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);
            assert V == Empty;

            Extract_Empty(F, Root, I, D, F_Old, V); 

            // Extract_Empty post condition:
            assert Tree_Structure(F);
            assert Valid_Root(F, Root);
            assert V == Peek(F_Old, I, D) && Peek(F, I, D) == Empty;
            assert forall J: Index_Type :: J != V ==> Parent_Of(F, J) == Parent_Of(F_Old, J);
            assert forall J: Index_Type :: J != V && Parent_Of(F, J) != Empty ==> Position_Of(F, J) == Position_Of(F_Old, J);
            assert forall J: Index_Type, E: Direction :: J != I || E != D ==> Peek(F, J, E) == Peek(F_Old, J, E);
            assert forall T: Index_Type :: Valid_Root(F_Old, T) && I != T && V != T ==> Valid_Root(F, T);
            assert forall T: Index_Type :: Valid_Root(F_Old, T) && Root != T && V != T ==> Model(F, T) == Model(F_Old, T);
            assert V != Empty ==> Valid_Root(F, V);
            assert forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> Model(F_Old, Root)[I].K;
            assert forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> 
                Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[I].A, Model(F_Old, Root)[I].A);
            assert forall I: Index_Type :: Model(F_Old, Root)[I].K ==>
                if V != Empty && Model(F_Old, Root)[V].A <= Model(F_Old, Root)[I].A then Model(F, V)[I].K else Model(F, Root)[I].K;
            assert forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F_Old, Root)[I].K;
            assert forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F, Root)[I].A == Model(F_Old, Root)[I].A;

            // post condition:
            assert Tree_Structure(F);
            assert Valid_Root(F, Root);
            assert V == Peek(F_Old, I, D) && Peek(F, I, D) == Empty;
            assert forall J: Index_Type :: J != V ==> Parent_Of(F, J) == Parent_Of(F_Old, J);
            assert forall J: Index_Type :: J != V && Parent_Of(F, J) != Empty ==> Position_Of(F, J) == Position_Of(F_Old, J);
            assert forall J: Index_Type, E: Direction :: J != I || E != D ==> Peek(F, J, E) == Peek(F_Old, J, E);
            assert forall T: Index_Type :: Valid_Root(F_Old, T) && I != T && V != T ==> Valid_Root(F, T);
            assert forall T: Index_Type :: Valid_Root(F_Old, T) && Root != T && V != T ==> Model(F, T) == Model(F_Old, T);
            assert V != Empty ==> Valid_Root(F, V);
            assert forall I: Index_Type :: Model(F_Old, Root)[I].K ==>
                if V != Empty && Model(F_Old, Root)[V].A <= Model(F_Old, Root)[I].A then Model(F, V)[I].K else Model(F, Root)[I].K;
            assert forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F_Old, Root)[I].K;
            assert forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> Model(F_Old, Root)[I].K;
            assert forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F, Root)[I].A == Model(F_Old, Root)[I].A;
            assert forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> 
                Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[I].A, Model(F_Old, Root)[I].A);
        }

        // post condition:
        assert Tree_Structure(F);
        assert Valid_Root(F, Root);
        assert V == Peek(F_Old, I, D) && Peek(F, I, D) == Empty;
        assert forall J: Index_Type :: J != V ==> Parent_Of(F, J) == Parent_Of(F_Old, J);
        assert forall J: Index_Type :: J != V && Parent_Of(F, J) != Empty ==> Position_Of(F, J) == Position_Of(F_Old, J);
        assert forall J: Index_Type, E: Direction :: J != I || E != D ==> Peek(F, J, E) == Peek(F_Old, J, E);
        assert forall T: Index_Type :: Valid_Root(F_Old, T) && I != T && V != T ==> Valid_Root(F, T);
        assert forall T: Index_Type :: Valid_Root(F_Old, T) && Root != T && V != T ==> Model(F, T) == Model(F_Old, T);
        assert V != Empty ==> Valid_Root(F, V);
        assert forall I: Index_Type :: Model(F_Old, Root)[I].K ==>
            if V != Empty && Model(F_Old, Root)[V].A <= Model(F_Old, Root)[I].A then Model(F, V)[I].K else Model(F, Root)[I].K;
        assert forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F_Old, Root)[I].K;
        assert forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> Model(F_Old, Root)[I].K;
        assert forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F, Root)[I].A == Model(F_Old, Root)[I].A;
        assert forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> 
            Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[I].A, Model(F_Old, Root)[I].A);
    } 






// These lemmas are fo the V==Empty case

    lemma Lemma_eq_arrays_implies_eq_diractions(F: Forest, F_Old: Forest)
        requires Tree_Structure(F)
        requires  Tree_Structure(F_Old)
        requires C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old)
        ensures forall J: Index_Type, E: Direction :: (Peek(F, J, E) == Peek(F_Old, J, E))
    {
        assert Tree_Structure(F);
        assert Tree_Structure(F_Old);
        assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);
        assert forall J: Index_Type :: C(F)[J] == C(F_Old)[J];
        assert forall J: Index_Type :: Position(C(F)[J]) == Position(C(F_Old)[J]);
        assert forall J: Index_Type :: Position_Of(F, J) == Position_Of(F_Old, J);
        assert forall J: Index_Type, E: Direction :: if E == Left then Left_Child(C(F)[J]) == Left_Child(C(F_Old)[J]) else Right_Child(C(F)[J]) == Right_Child(C(F_Old)[J]);
        assert forall J: Index_Type, E: Direction :: (Peek(F, J, E) == Peek(F_Old, J, E));
    }


    lemma  Lemma_eq_arrays_implies_eq_positions(F: Forest, F_Old: Forest)
        requires Tree_Structure(F)
        requires  Tree_Structure(F_Old)
        requires C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old)
        ensures forall J: Index_Type :: Position_Of(F, J) == Position_Of(F_Old, J)
    {
        assert Tree_Structure(F);
        assert Tree_Structure(F_Old);
        assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);
        assert forall J: Index_Type :: C(F)[J] == C(F_Old)[J];
        assert forall J: Index_Type :: Position(C(F)[J]) == Position(C(F_Old)[J]);
        assert forall J: Index_Type :: Position_Of(F, J) == Position_Of(F_Old, J);
    } 

    lemma  Lemma_eq_arrays_implies_eq_parents_children(F: Forest, F_Old: Forest)
        requires Tree_Structure(F)
        requires  Tree_Structure(F_Old)
        requires C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old)
        ensures forall J: Index_Type :: Parent_Of(F, J) == Parent_Of(F_Old, J)
    {
        assert Tree_Structure(F);
        assert Tree_Structure(F_Old);
        assert C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old);
        assert forall J: Index_Type :: C(F)[J] == C(F_Old)[J];
        assert forall J: Index_Type :: Parent(C(F)[J]) == Parent(C(F_Old)[J]);
        assert forall J: Index_Type :: Parent_Of(F, J) == Parent_Of(F_Old, J);
    } 

    lemma{:verify false} Lemma_Model_Parent_implies_Model_child(F_Old: Forest, Root: Index_Type, I: Index_Type, D: Direction, V:Extended_Index_Type)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires Model(F_Old, Root)[I].K
        requires V != Empty
        requires Parent(C(F_Old)[V]) == I
        ensures Model(F_Old, Root)[V].K
    {
        /* If I belongs to the tree rooted at Root in the original forest F_Old,
           V's parent in F_Old is I,
           then V belongs to the tree rooted at Root in F_Old. */
    }


    lemma {:verify false} Lemma_eq_arrays_implies_Tree_Structure(F: Forest, F_Old: Forest)
        requires C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old)
        requires Tree_Structure(F)
        ensures Tree_Structure(F_Old)
    {
        // If F is a valid forest, F and F_old are of the same size and have the same nodes' array,
        // then F_Old is also a valid forest.
    }

    lemma {:verify false} Lemma_eq_arrays_implies_eq_models(F: Forest, F_Old: Forest)
        requires C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        ensures forall T: Index_Type :: Valid_Root(F, T) ==> Valid_Root(F_Old, T) && (Model(F, T) == Model(F_Old, T))
    {
        // Since the the forests are the same (same arrays and same sizes), all parents and children of all nodes (indexes) are the same, 
        // and hence, all the paths from all roots (the models) are the same.
    }

    lemma{:verify false} Lemma_Tree_Structure(F: Forest, Root: Index_Type, I: Index_Type, D: Direction, V:Extended_Index_Type)
        requires V != Empty
        requires Position(C(F)[V]) == Top
        requires Parent(C(F)[V]) == Empty
        requires D == Left ==> Left_Child(C(F)[I]) == Empty
        requires D == Right ==> Right_Child(C(F)[I]) == Empty
        requires forall J: Index_Type :: S(F) < J < Max ==> C(F)[J] == (Empty, Empty, Empty, Top)
        requires forall J: Index_Type :: J != V ==> Empty <= Parent(C(F)[J]) < S(F)
        requires forall J: Index_Type :: J != I ==> Empty <= Left_Child(C(F)[J]) < S(F) 
        requires forall J: Index_Type :: J != I ==> Empty <= Right_Child(C(F)[J]) < S(F)
        requires if D == Left then Left_Child(C(F)[I]) == Empty else Empty <= Left_Child(C(F)[I]) < S(F)
        requires if D == Right then Right_Child(C(F)[I]) == Empty else Empty <= Right_Child(C(F)[I]) < S(F)
        requires forall J: Index_Type :: J != V  ==> (Position(C(F)[J]) == Top ==> Parent(C(F)[J]) == Empty)
        requires Position(C(F)[V]) == Top ==> Parent(C(F)[V]) == Empty
        requires forall J: Index_Type :: J != I ==> (Left_Child(C(F)[J]) != Empty ==> 
                Position(C(F)[Left_Child(C(F)[J])]) == Left && Parent(C(F)[Left_Child(C(F)[J])]) == J) // prove J's left child != V
        requires forall J: Index_Type :: J != I ==> (Right_Child(C(F)[J]) != Empty ==>
                Position(C(F)[Right_Child(C(F)[J])]) == Left && Parent(C(F)[Right_Child(C(F)[J])]) == J) // prove J's right child != V
        requires if D == Left then Left_Child(C(F)[I]) == Empty else (Left_Child(C(F)[I]) != Empty ==> 
                Position(C(F)[Left_Child(C(F)[I])]) == Left && Parent(C(F)[Left_Child(C(F)[I])]) == I) // prove I's left child != V)
        requires if D == Right then Right_Child(C(F)[I]) == Empty else (Right_Child(C(F)[I]) != Empty ==> 
                Position(C(F)[Right_Child(C(F)[I])]) == Right && Parent(C(F)[Right_Child(C(F)[I])]) == I) // prove I's right child != V)
        requires forall J: Index_Type :: Parent(C(F)[J]) != I  ==> (Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Left ==> Left_Child(C(F)[Parent(C(F)[J])]) == J)
        requires forall J: Index_Type :: Parent(C(F)[J]) != I ==> (Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Right ==> Right_Child(C(F)[Parent(C(F)[J])]) == J)
        requires forall J: Index_Type :: Parent(C(F)[J]) == I ==> (if J != V then (Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Left ==> Left_Child(C(F)[Parent(C(F)[J])]) == J) else Parent(C(F)[J]) == Empty)
        requires forall J: Index_Type :: Parent(C(F)[J]) == I ==> (if J != V then (Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Right ==> Right_Child(C(F)[Parent(C(F)[J])]) == J) else Parent(C(F)[J]) == Empty)
        
        ensures forall J: Index_Type :: S(F) < J < Max ==> C(F)[J] == (Empty, Empty, Empty, Top)
        ensures forall J: Index_Type :: Empty <= Parent(C(F)[J]) < S(F)
        ensures forall J: Index_Type :: Empty <= Left_Child(C(F)[J]) < S(F) 
        ensures forall J: Index_Type :: Empty <= Right_Child(C(F)[J]) < S(F)
        ensures forall J: Index_Type :: Position(C(F)[J]) == Top ==> Parent(C(F)[J]) == Empty
        ensures forall J: Index_Type :: Left_Child(C(F)[J]) != Empty ==> 
                Position(C(F)[Left_Child(C(F)[J])]) == Left && Parent(C(F)[Left_Child(C(F)[J])]) == J
        ensures forall J: Index_Type :: Right_Child(C(F)[J]) != Empty ==>
                Position(C(F)[Right_Child(C(F)[J])]) == Right && Parent(C(F)[Right_Child(C(F)[J])]) == J
        ensures forall J: Index_Type :: Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Left ==> Left_Child(C(F)[Parent(C(F)[J])]) == J
        ensures forall J: Index_Type :: Parent(C(F)[J]) != Empty && Position(C(F)[J]) == Right ==> Right_Child(C(F)[Parent(C(F)[J])]) == J
    {
        // this lemma promise that after the extraction of V the left\right child of I the structure of the tree is still valid.
        // the lemma requires the every node that is not V or I will fulfill the requiremants of the valid Tree structures.
        // for example the lemma requires "forall J: Index_Type :: J != V  ==> (Position(C(F)[J]) == Top ==> Parent(C(F)[J]) == Empty)"
        // we know that its is true because the method "Extract" got a valid forest and didnt change any other nodes in the forest
        // and for V/I the lemma require the spesifice changes that the method changed and are indeed fulfill the tree structure requiremants.
        // for example the lemma requires from V: Position(C(F)[V]) == Top ==> Parent(C(F)[V]) == Empty
        // because we know that for all J=!V some property is true and we know that for J==V it is true we know it for all J.
        // hence we know that after the extraction the Forest is still fulfill the Tree Structure requirments.
    }





    lemma Prove_Post(F: Forest, Root: Index_Type, I: Index_Type, D: Direction, F_Old: Forest, V:Extended_Index_Type)
        requires V != Empty
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)

        // The size of the forest does not change
        requires S(F) == S(F_Old)
        
        // Root was the root of a tree
        requires Valid_Root(F_Old, Root)
        requires Valid_Root(F, Root)

        // Root and V are different nodes
        requires V != Root

        // V is the root of a tree
        requires Valid_Root(F, V)

        // V was in the tree
        requires Model(F_Old, Root)[V].K

        // Except for V, the value of parent link is preserved
        requires forall I: Index_Type :: (I != V) ==> Parent_Of(F, I) == Parent_Of(F_Old, I)

        // Except for V, the value of position is preserved
        requires forall I: Index_Type :: (I != V) ==> Position_Of(F, I) == Position_Of(F_Old, I)

        // For nodes previously not in the tree, the value of left and right child is preserved.
        requires forall J: Index_Type, E: Direction :: (!Model(F_Old, Root)[J].K) ==> (Peek(F, J, E) == Peek(F_Old, J, E))

        // Nodes previously in the tree rooted at Root either remain nodes in
        // the tree rooted at Root, or for those nodes which have V on their
        // path, become nodes in the tree rooted at V.
        ensures forall I: Index_Type :: Model(F_Old, Root)[I].K ==>
                if V != Empty && Model(F_Old, Root)[V].A <= Model(F_Old, Root)[I].A then Model(F, V)[I].K else Model(F, Root)[I].K

        // Nodes in the tree rooted at Root were previously in the tree rooted at Root.
        ensures forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F_Old, Root)[I].K

        // Nodes in the tree rooted at V were previously in the tree rooted at Root.
        ensures forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> Model(F_Old, Root)[I].K

        // Paths are preserved for nodes in the tree rooted at Root
        ensures forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F, Root)[I].A == Model(F_Old, Root)[I].A

        // The path for nodes in the tree rooted at V is obtained by
        // subtracting the path from Root to V from the path from Root to the node.
        ensures forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> 
                Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[I].A, Model(F_Old, Root)[I].A)

        //  All other trees in the forest are preserved
        ensures forall T: Index_Type :: Valid_Root(F_Old, T) && Root != T && V != T ==> Model(F, T) == Model(F_Old, T)
    {
        assert Tree_Structure(F);
        assert Tree_Structure(F_Old);
        assert Valid_Root(F_Old, Root);
        assert Valid_Root(F, Root);
        assert V != Empty;
        assert Valid_Root(F, V);
        assert V != Root;
        assert Model(F_Old, Root)[V].K;
        L_subpath(F, Root, F_Old, V);
        assert forall N: Index_Type, J: Index_Type :: (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==> 
            (Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A ==> Model(F, V)[J].K) &&
            (!(Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A) ==> Model(F, Root)[J].K);


        assert Tree_Structure(F);
        assert Tree_Structure(F_Old);
        assert Valid_Root(F, Root);
        assert Valid_Root(F_Old, Root);
        L_untouched_nodes_in_Root(F, F_Old, Root);
        assert forall N: Index_Type, J: Index_Type :: (Model(F, Root)[J].K && |Model(F, Root)[J].A| <= N - 1) ==> Model(F_Old, Root)[J].K;


        assert Tree_Structure(F);
        assert Tree_Structure(F_Old);
        assert Valid_Root(F_Old, Root);
        assert V != Empty;
        assert Valid_Root(F, V);
        assert V != Root;
        L_Vs_descendant_where_in_Root(F, F_Old, Root, V);
        assert forall N: Index_Type, J: Index_Type :: (Model(F, V)[J].K && |Model(F, V)[J].A| <= N - 1) ==> Model(F_Old, Root)[J].K;


        assert Tree_Structure(F);
        assert Tree_Structure(F_Old);
        assert Valid_Root(F_Old, Root);
        L_Roots_nodes_same_path(F, F_Old, Root);
        assert forall N: Index_Type, J: Index_Type :: (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==>
                                                        (Model(F, Root)[J].K ==> Model(F, Root)[J].A == Model(F_Old, Root)[J].A);


        assert Tree_Structure(F);
        assert Tree_Structure(F_Old);
        assert Valid_Root(F_Old, Root);
        assert V != Empty;
        assert V != Root;
        assert Valid_Root(F, V);
        L_path_concatination(F, F_Old, Root, V);
        assert forall N: Index_Type, J: Index_Type :: (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==>
                (Model(F, V)[J].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[J].A, Model(F_Old, Root)[J].A));


        assert Tree_Structure(F);
        assert Tree_Structure(F_Old);
        assert Valid_Root(F, Root);
        assert Valid_Root(F_Old, Root);
        L_preserve_equal(F, F_Old, Root);
        assert forall N: Index_Type, J: Index_Type :: ((Model(F_Old, Root)[J].K) && (|Model(F_Old, Root)[J].A| == N) && (Model(F, Root)[J].K)) ==>
                (Preserve_Equal(Model(F, Root)[Parent(C(F)[J])].A,
                                Model(F_Old, Root)[Parent(C(F_Old)[J])].A,
                                Model(F, Root)[J].A,
                                Model(F_Old, Root)[J].A,
                                Position(C(F)[J])));


        assert Tree_Structure(F);
        assert Tree_Structure(F_Old);
        assert Valid_Root(F, Root);
        assert Valid_Root(F_Old, Root);
        assert Valid_Root(F, V);
        L_preserve_concat(F, F_Old, Root, V);
        assert forall N: Index_Type, J: Index_Type :: ((Model(F_Old, Root)[J].K) && (|Model(F_Old, Root)[J].A| == N) && (Model(F, V)[J].K)) && (J!=V)==>
               (Preserve_Concat(Model(F, V)[Parent(C(F)[J])].A,
                                Model(F_Old, Root)[Parent(C(F_Old)[J])].A,
                                Model(F, V)[J].A,
                                Model(F_Old, Root)[J].A,
                                Model(F_Old, Root)[V].A,
                                Position(C(F)[J])));
        

        assert Tree_Structure(F);
        assert Tree_Structure(F_Old);
        assert Valid_Root(F_Old, Root);
        assert Valid_Root(F, Root);
        L_Roots_nodes_same_path2(F, F_Old, Root);
        assert forall N: Index_Type, J: Index_Type, j: Index_Type :: 
                        (0 <= j < J) && 
                        (Model(F_Old, Root)[j].K) && 
                        (|Model(F_Old,Root)[j].A| <= N) ==>
                        (Model(F, Root)[j].K ==> Model(F, Root)[j].A == Model(F_Old, Root)[j].A);


        assert Tree_Structure(F);
        assert Tree_Structure(F_Old);
        assert Valid_Root(F_Old, Root);
        assert V != Empty;
        assert V != Root;
        assert Valid_Root(F, V);
        L_path_concatination2(F, F_Old, Root, V);
        assert forall N: Index_Type, J: Index_Type, j: Index_Type :: 
                        (0 <= j < J) &&
                        (Model(F_Old, Root)[j].K && |Model(F_Old, Root)[j].A| <= N - 1) ==>
                        (Model(F, V)[j].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[j].A, Model(F_Old, Root)[j].A));


        assert Tree_Structure(F);
        assert Tree_Structure(F_Old);
        assert Valid_Root(F_Old, Root);
        assert V != Empty;
        assert V != Root;
        assert Valid_Root(F, V);
        L_other_trees(F, F_Old, Root, V);
        assert forall R: Extended_Index_Type_With_Max, P: Extended_Index_Type_With_Max :: 
                        (0 <= R < S(F_Old)) && (Position(C(F_Old)[R]) == Top) && (R != Root) && (R != V) ==>
                            ((0 <= P <= R) && (Position(C(F_Old)[P]) == Top) && (P != Root) && (P != V) ==>
                                Model(F_Old, P) == Model(F, P));  

    }





    // pragma Loop_Invariant
        //           (for all I in Index_Type =>
        //             (if Model (F_Old, Root) (I).K and then Last (Model (F_Old, Root) (I).A) <= N - 1 then
        //               (if Model (F_Old, Root) (V).A <= Model (F_Old, Root) (I).A
        //                then Model (F, V) (I).K
        //                else Model (F, Root) (I).K)));
    lemma L_subpath(F: Forest, Root: Index_Type, F_Old: Forest, V:Extended_Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires Valid_Root(F, Root)
        requires V != Empty
        requires Valid_Root(F, V)
        requires V != Root
        requires Model(F_Old, Root)[V].K
        ensures forall N: Index_Type, J: Index_Type :: (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==> 
            (Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A ==> Model(F, V)[J].K) &&
            (!(Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A) ==> Model(F, Root)[J].K)
    {
        forall N: Index_Type, J: Index_Type {
            if(Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1){
                L_rec_subpath(F, Root, J, F_Old, V, N);
                assert  (Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A ==> Model(F, V)[J].K);
                assert (!(Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A) ==> Model(F, Root)[J].K);
                assert (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==> 
                    (Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A ==> Model(F, V)[J].K) &&
                    (!(Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A) ==> Model(F, Root)[J].K);
            }
            else{
                assert !(Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1);
                assert (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==> 
                        (Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A ==> Model(F, V)[J].K) &&
                        (!(Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A) ==> Model(F, Root)[J].K);
            }
            assert (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==> 
                    (Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A ==> Model(F, V)[J].K) &&
                    (!(Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A) ==> Model(F, Root)[J].K);
        }
        assert forall N: Index_Type, J: Index_Type :: (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==> 
            (Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A ==> Model(F, V)[J].K) &&
            (!(Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A) ==> Model(F, Root)[J].K);
    }

    lemma L_rec_subpath(F: Forest, Root: Index_Type, J: Index_Type, F_Old: Forest, V:Extended_Index_Type, N: Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires Valid_Root(F, Root)
        requires V != Empty
        requires Valid_Root(F, V)
        requires V != Root
        requires Model(F_Old, Root)[V].K
        requires (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1)
        ensures Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A ==> Model(F, V)[J].K
        ensures !(Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A) ==> Model(F, Root)[J].K
        decreases N
    {
        if (N == 0){
            // base case
            L0_subpath(F, Root, J, F_Old, V, N);
        }
        else if (N == 1)
        {
            // base case
            L1_subpath(F, Root, J, F_Old, V, N);
        }
        else if(J == V){
            assert Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A;
            assert Model(F,V)[J].K;
            assert Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A ==> Model(F,V)[J].K;
            assert !(Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A) ==> Model(F,Root)[J].K;
        }
        else if (J == Root){
            assert |Model(F_Old, Root)[J].A| == 0;
            assert J != V;
            assert V != Root;
            assert !(Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A); // Since |Model(F_Old, Root)[J].A| == 0 and |(Model(F_Old, Root)[V].A| != 0 (V != Root)
            assert Model(F,Root)[J].K; // Since J == Root
            assert !(Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A) ==> Model(F,Root)[J].K; // everything ==> true
            assert Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A ==> Model(F,V)[J].K; // false ==> everything
        }
        else
        {
            assert J != Root;
            assert |Model(F_Old, Root)[J].A| > 0;
            Parent_in_path_to_child(F, Root, J);
            assert Parent(C(F_Old)[J]) != Empty;
            ghost var p := Parent_Of(F_Old, J);
            L_rec_subpath(F, Root, p, F_Old, V, N - 1);
        }
    } 

    lemma L0_subpath(F: Forest, Root: Index_Type, J: Index_Type, F_Old: Forest, V:Extended_Index_Type, N: Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires Valid_Root(F, Root)
        requires V != Empty
        requires Valid_Root(F, V)
        requires N == 0
        requires (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1)
        ensures Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A ==> Model(F,V)[J].K
        ensures !(Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A) ==> Model(F,Root)[J].K
    {
    }

    lemma L1_subpath(F: Forest, Root: Index_Type, J: Index_Type, F_Old: Forest, V:Extended_Index_Type, N: Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires Valid_Root(F, Root)
        requires V != Empty
        requires Valid_Root(F, V)
        requires V != Root
        requires N == 1
        requires Model(F_Old, Root)[V].K
        requires (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1)
        ensures Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A ==> Model(F,V)[J].K
        ensures !(Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A) ==> Model(F,Root)[J].K
    {
        assert Tree_Structure(F);
        assert Tree_Structure(F_Old);
        assert Valid_Root(F_Old, Root);
        assert Valid_Root(F, Root);
        assert V != Empty;
        assert Valid_Root(F, V);
        assert V != Root;
        assert Model(F_Old, Root)[V].K;
        L_length_of_non_empty_path(Root, F_Old, V);
        assert |Model(F_Old, Root)[V].A| > 0;
        assert N == 1;
        assert (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1);
        assert |Model(F_Old, Root)[J].A| <= 0;
        assert 0 <= |Model(F_Old, Root)[J].A| <= 0;
        assert |Model(F_Old, Root)[J].A| == 0;
        assert Model(F_Old, Root)[J].A == [];
        assert !(Model(F_Old, Root)[V].A <= []);
        assert !(Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A);
        // First ensures:
        assert (Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A ==> Model(F,V)[J].K); // false ==> everything

        assert Model(F_Old, Root)[J].K;
        assert Model(F_Old, Root)[J].A == [];
        L_empty_path_implies_same_node(Root, F_Old, J);
        assert Root == J;
        assert Tree_Structure(F);
        assert Valid_Root(F, Root);
        L_root_in_root(Root, F);
        assert Model(F,Root)[Root].K;
        assert Model(F,Root)[J].K;
        // Second ensures:
        assert !(Model(F_Old, Root)[V].A <= Model(F_Old, Root)[J].A) ==> Model(F,Root)[J].K; // Second ensures
    }

    lemma{:verify false} L_length_of_non_empty_path(Root: Index_Type, F_Old: Forest, V:Extended_Index_Type)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires V != Empty
        requires V != Root
        requires Model(F_Old, Root)[V].K
        ensures |Model(F_Old, Root)[V].A| > 0
    {
        // If V is in the tree rooted at Root, and V != Root,
        // then the length of the path from Root to V is larger then 0
    }

    lemma{:verify false} L_empty_path_implies_same_node(Root: Index_Type, F_Old: Forest, J: Index_Type)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires Model(F_Old, Root)[J].K
        requires Model(F_Old, Root)[J].A == []
        ensures Root == J
    {
        // If J belongs to the tree rooted at Root, J != Root,
        // and the path from Root to J is the empty path,
        // then Root == J
    }

    lemma{:verify false} L_root_in_root(Root: Index_Type, F: Forest)
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        ensures Model(F,Root)[Root].K
    {
        // If F is a forest and Root is a valid root in F, than Root belongs to the tree rooted at Root
    }


    lemma{:verify false} Parent_in_path_to_child(F: Forest, Root: Index_Type, J: Index_Type)
        requires Tree_Structure(F)
        requires Valid_Root(F, Root)
        requires Model(F, Root)[J].K
        requires |Model(F, Root)[J].A| > 0
        ensures Parent(C(F)[J]) != Empty
    {
        // If the path from Root to node J is of length larger than 0,
        // then there must be at least two vertices in that path.
        // The path must begin with Root and end with J, so J != Root,
        // thus J must have a non- empty parent.
    }

    // pragma Loop_Invariant
        //    (for all I in Index_Type =>
        //    (if Model (F, Root) (I).K and then Last (Model (F, Root) (I).A) <= N - 1
        //    then Model (F_Old, Root) (I).K));
    lemma L_untouched_nodes_in_Root(F: Forest, F_Old: Forest, Root: Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F, Root)
        requires Valid_Root(F_Old, Root)
        ensures forall N: Index_Type, J: Index_Type :: (Model(F, Root)[J].K && |Model(F, Root)[J].A| <= N - 1) ==> Model(F_Old, Root)[J].K
    {
        forall N: Index_Type, J: Index_Type {
            if(Model(F, Root)[J].K && |Model(F, Root)[J].A| <= N - 1)
            {
                assert Model(F, Root)[J].K && |Model(F, Root)[J].A| <= N - 1;
                L_rec_untouched_nodes_in_Root(F, F_Old, Root, N, J);
                assert Model(F_Old, Root)[J].K;
                assert (Model(F, Root)[J].K && |Model(F, Root)[J].A| <= N - 1) ==> Model(F_Old, Root)[J].K;                
            }
            else
            {
                assert !(Model(F, Root)[J].K && |Model(F, Root)[J].A| <= N - 1);
                assert (Model(F, Root)[J].K && |Model(F, Root)[J].A| <= N - 1) ==> Model(F_Old, Root)[J].K; // false ==> everything
            }
            assert (Model(F, Root)[J].K && |Model(F, Root)[J].A| <= N - 1) ==> Model(F_Old, Root)[J].K;
        }
        assert forall N: Index_Type, J: Index_Type :: (Model(F, Root)[J].K && |Model(F, Root)[J].A| <= N - 1) ==> Model(F_Old, Root)[J].K;
    }

    lemma{:verify false} L_rec_untouched_nodes_in_Root(F: Forest, F_Old: Forest, Root: Index_Type, N: Index_Type, J: Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F, Root)
        requires Valid_Root(F_Old, Root)
        requires (Model(F, Root)[J].K && |Model(F, Root)[J].A| <= N - 1)
        ensures Model(F_Old, Root)[J].K
    {
        // Nodes that belongs to the tree rooted in Root in the new forest F,
        // were in the tree rooted in Root in the original forest F_Old.
    } 


    //  pragma Loop_Invariant
        // (for all I in Index_Type =>
        // (if Model (F, V) (I).K and then Last (Model (F, V) (I).A) <= N - 1
        // then Model (F_Old, Root) (I).K));
    lemma L_Vs_descendant_where_in_Root(F: Forest, F_Old: Forest, Root: Index_Type, V: Extended_Index_Type) 
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires V != Empty
        requires Valid_Root(F, V)
        requires V != Root
        ensures forall N: Index_Type, J: Index_Type :: (Model(F, V)[J].K && |Model(F, V)[J].A| <= N - 1) ==> Model(F_Old, Root)[J].K
    {
        forall N: Index_Type, J: Index_Type {
            if(Model(F, V)[J].K && |Model(F, V)[J].A| <= N - 1){
                assert Model(F, V)[J].K && |Model(F, V)[J].A| <= N - 1;
                L_rec_Vs_descendant_where_in_Root(F, F_Old, Root, V, N, J);
                assert Model(F_Old, Root)[J].K;
                assert (Model(F, V)[J].K && |Model(F, V)[J].A| <= N - 1) ==> Model(F_Old, Root)[J].K;
            }
            else{
                assert !(Model(F, V)[J].K && |Model(F, V)[J].A| <= N - 1);
                assert (Model(F, V)[J].K && |Model(F, V)[J].A| <= N - 1) ==> Model(F_Old, Root)[J].K; // false ==> everything
            }
            assert (Model(F, V)[J].K && |Model(F, V)[J].A| <= N - 1) ==> Model(F_Old, Root)[J].K;
        }
        assert forall N: Index_Type, J: Index_Type :: (Model(F, V)[J].K && |Model(F, V)[J].A| <= N - 1) ==> Model(F_Old, Root)[J].K;
    }

    lemma{:verify false} L_rec_Vs_descendant_where_in_Root(F: Forest, F_Old: Forest, Root: Index_Type, V: Extended_Index_Type, N: Index_Type, J: Index_Type) 
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires V != Empty
        requires Valid_Root(F, V)
        requires V != Root
        requires (Model(F, V)[J].K && |Model(F, V)[J].A| <= N - 1)
        ensures Model(F_Old, Root)[J].K
    {
        // Node that belongs to the tree rooted at V in the new forest F,
        // were in the tree rooted at Root in the original forest F_Old
    } 


    //  pragma Loop_Invariant
        // (for all I in Index_Type =>
        // (if Model (F_Old, Root) (I).K and then Last (Model (F_Old, Root) (I).A) <= N - 1 then
        // (if Model (F, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A)));
    lemma L_Roots_nodes_same_path(F: Forest, F_Old: Forest, Root: Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        ensures forall N: Index_Type, J: Index_Type :: (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==>
                                                        (Model(F, Root)[J].K ==> Model(F, Root)[J].A == Model(F_Old, Root)[J].A)
    {
        forall N: Index_Type, J: Index_Type {
            if(Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1){
                assert Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1;
                L_rec_Roots_nodes_same_path(F, F_Old, Root, N, J);
                assert Model(F, Root)[J].K ==> Model(F, Root)[J].A == Model(F_Old, Root)[J].A;
                assert (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==> 
                        (Model(F, Root)[J].K ==> Model(F, Root)[J].A == Model(F_Old, Root)[J].A);
            }
            else{
                assert !(Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1);
                assert (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==> 
                        (Model(F, Root)[J].K ==> Model(F, Root)[J].A == Model(F_Old, Root)[J].A); // false ==> everything
            }
            assert (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==> 
                    (Model(F, Root)[J].K ==> Model(F, Root)[J].A == Model(F_Old, Root)[J].A);
        }
        assert forall N: Index_Type, J: Index_Type :: (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==>
                                                        (Model(F, Root)[J].K ==> Model(F, Root)[J].A == Model(F_Old, Root)[J].A);
    }

    lemma{:verify false} L_rec_Roots_nodes_same_path(F: Forest, F_Old: Forest, Root: Index_Type, N: Index_Type, J: Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1)
        ensures (Model(F, Root)[J].K ==> Model(F, Root)[J].A == Model(F_Old, Root)[J].A)
    {
        // For nodes that belong to the tree rooted at Root in the original forest F_Old,
        // and belong to the tree rooted at V in the new forest F,
        // the path in F_Old from Root to the node is the same as the path in F from V to the node.
    } 


    // pragma Loop_Invariant
        // (for all I in Index_Type =>
            // (if Model (F_Old, Root) (I).K and then Last (Model (F_Old, Root) (I).A) <= N - 1 then
             // (if Model (F, V) (I).K then
                    // Is_Concat (Q => Model (F_Old, Root) (V).A,
                    // V => Model (F, V) (I).A,
                    // P => Model (F_Old, Root) (I).A))));
    lemma L_path_concatination(F: Forest, F_Old: Forest, Root: Index_Type, V: Extended_Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires V != Empty
        requires V != Root
        requires Valid_Root(F, V)
        ensures forall N: Index_Type, J: Index_Type :: (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==>
                (Model(F, V)[J].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[J].A, Model(F_Old, Root)[J].A))
    {
        forall N: Index_Type, J: Index_Type {
            if(Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1)
            {
                assert (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1);
                if(Model(F, V)[J].K)
                {
                    assert Model(F, V)[J].K;
                    assert (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1);
                    L_rec_path_concatination(F, F_Old, Root, V, N, J);
                    assert Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[J].A, Model(F_Old, Root)[J].A);
                    assert (Model(F, V)[J].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[J].A, Model(F_Old, Root)[J].A));
                }
                else
                {
                    assert !Model(F, V)[J].K;
                    assert (Model(F, V)[J].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[J].A, Model(F_Old, Root)[J].A)); // false ==> everything
                }
                assert (Model(F, V)[J].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[J].A, Model(F_Old, Root)[J].A));
                assert (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==>
                        (Model(F, V)[J].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[J].A, Model(F_Old, Root)[J].A));
            }
            else
            {
                assert !(Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1);
                assert (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==>
                        (Model(F, V)[J].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[J].A, Model(F_Old, Root)[J].A)); // false ==> everythong
            }
            assert (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==>
                    (Model(F, V)[J].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[J].A, Model(F_Old, Root)[J].A));
        }
        assert forall N: Index_Type, J: Index_Type :: (Model(F_Old, Root)[J].K && |Model(F_Old, Root)[J].A| <= N - 1) ==>
                (Model(F, V)[J].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[J].A, Model(F_Old, Root)[J].A));
    }

    lemma{:verify false} L_rec_path_concatination(F: Forest, F_Old: Forest, Root: Index_Type, V: Extended_Index_Type, N: Index_Type, J: Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires V != Empty
        requires V != Root
        requires Valid_Root(F, V)
        requires Model(F_Old, Root)[J].K
        requires |Model(F_Old, Root)[J].A| <= N - 1
        ensures (Model(F, V)[J].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[J].A, Model(F_Old, Root)[J].A))
    {
        // For nodes that belong the tree rooted at Root in the original forest F_Old,
        // if they belong to the tree rooted at V in the new forest F,
        // then the path from Root to the nodes in F_Old equals to the concatination
        // of the path from Root to V in F_Old, with the path from V to the nodes in F.
    } 

    lemma{:verify false} L_preserve_concat(F: Forest, F_Old: Forest, Root: Index_Type, V: Extended_Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F, Root)
        requires Valid_Root(F_Old, Root)
        requires Valid_Root(F, V)
        ensures forall N: Index_Type, J: Index_Type :: ((Model(F_Old, Root)[J].K) && (|Model(F_Old, Root)[J].A| == N) && (Model(F, V)[J].K)) && (J!=V)==>
               (Preserve_Concat(Model(F, V)[Parent(C(F)[J])].A,
                                Model(F_Old, Root)[Parent(C(F_Old)[J])].A,
                                Model(F, V)[J].A,
                                Model(F_Old, Root)[J].A,
                                Model(F_Old, Root)[V].A,
                                Position(C(F)[J])))
    {
        // this lemma promise that if in the old Forest some node J != V had a path from the Root in length N
        // and in the new forst it has a path from V (in V's Tree) then the paths from Root to J in the old forest is the concatenation of 
        // the path from root to V in the old tree and from V ti J in the new tree.
    } 

    //  procedure Preserve_Concat (S1, S2, S3, S4, T : Sequence; D : Direction) with
    //     Ghost,
    //     Global => null,
    //     Pre  => Length (T) <= Max
    //     and then Is_Concat (T, S1, S2)
    //     and then Is_Add (S1, D, S3)
    //     and then Is_Add (S2, D, S4),
    //     Post => Is_Concat (T, S3, S4);
    ghost predicate Preserve_Concat(S1: D_Seq, S2: D_Seq, S3: D_Seq, S4: D_Seq, T: D_Seq, D: Direction)
    {
        ((|T| <= Max) && Is_Concat(T, S1, S2) && Is_Add(S1, D, S3) && Is_Add(S2, D, S4)) ==> Is_Concat(T, S3, S4)
    }


    // for KI in Index_Type loop
    //     if Model (F_Old, Root) (KI).K
    //                 and then Last (Model (F_Old, Root) (KI).A) = N
    //                 and then Model (F, Root) (KI).K
    //             then
    //                 Preserve_Equal (S1 => Model (F, Root) (F.C (KI).Parent).A,
    //                                 S2 => Model (F_Old, Root) (F.C (KI).Parent).A,
    //                                 S3 => Model (F, Root) (KI).A,
    //                                 S4 => Model (F_Old, Root) (KI).A,
    //                                 D  => F.C (KI).Position);
    lemma L_preserve_equal(F: Forest, F_Old: Forest, Root: Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F, Root)
        requires Valid_Root(F_Old, Root)
        ensures forall N: Index_Type, J: Index_Type :: ((Model(F_Old, Root)[J].K) && (|Model(F_Old, Root)[J].A| == N) && (Model(F, Root)[J].K)) ==>
                (Preserve_Equal(Model(F, Root)[Parent(C(F)[J])].A,
                                Model(F_Old, Root)[Parent(C(F_Old)[J])].A,
                                Model(F, Root)[J].A,
                                Model(F_Old, Root)[J].A,
                                Position(C(F)[J])))
    {
        forall N: Index_Type, J: Index_Type {
            if((Model(F_Old, Root)[J].K) && (|Model(F_Old, Root)[J].A| == N) && (Model(F, Root)[J].K))
            {
                assert ((Model(F_Old, Root)[J].K) && (|Model(F_Old, Root)[J].A| == N) && (Model(F, Root)[J].K));
                L_rec_preserve_equal(F, F_Old, Root, N, J);
                assert (Preserve_Equal(Model(F, Root)[Parent(C(F)[J])].A,
                                        Model(F_Old, Root)[Parent(C(F_Old)[J])].A,
                                        Model(F, Root)[J].A,
                                        Model(F_Old, Root)[J].A,
                                        Position(C(F)[J])));
                assert ((Model(F_Old, Root)[J].K) && (|Model(F_Old, Root)[J].A| == N) && (Model(F, Root)[J].K)) ==>
                        (Preserve_Equal(Model(F, Root)[Parent(C(F)[J])].A,
                                        Model(F_Old, Root)[Parent(C(F_Old)[J])].A,
                                        Model(F, Root)[J].A,
                                        Model(F_Old, Root)[J].A,
                                        Position(C(F)[J])));
            }
            else
            {
                assert !((Model(F_Old, Root)[J].K) && (|Model(F_Old, Root)[J].A| == N) && (Model(F, Root)[J].K));
                assert ((Model(F_Old, Root)[J].K) && (|Model(F_Old, Root)[J].A| == N) && (Model(F, Root)[J].K)) ==>
                        (Preserve_Equal(Model(F, Root)[Parent(C(F)[J])].A,
                                        Model(F_Old, Root)[Parent(C(F_Old)[J])].A,
                                        Model(F, Root)[J].A,
                                        Model(F_Old, Root)[J].A,
                                        Position(C(F)[J]))); // false ==> everything
            }
            assert ((Model(F_Old, Root)[J].K) && (|Model(F_Old, Root)[J].A| == N) && (Model(F, Root)[J].K)) ==>
                    (Preserve_Equal(Model(F, Root)[Parent(C(F)[J])].A,
                                    Model(F_Old, Root)[Parent(C(F_Old)[J])].A,
                                    Model(F, Root)[J].A,
                                    Model(F_Old, Root)[J].A,
                                    Position(C(F)[J])));

        }

        assert forall N: Index_Type, J: Index_Type :: ((Model(F_Old, Root)[J].K) && (|Model(F_Old, Root)[J].A| == N) && (Model(F, Root)[J].K)) ==>
                (Preserve_Equal(Model(F, Root)[Parent(C(F)[J])].A,
                                Model(F_Old, Root)[Parent(C(F_Old)[J])].A,
                                Model(F, Root)[J].A,
                                Model(F_Old, Root)[J].A,
                                Position(C(F)[J])));
    }

    lemma{:verify false} L_rec_preserve_equal(F: Forest, F_Old: Forest, Root: Index_Type, N: Index_Type, J: Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F, Root)
        requires Valid_Root(F_Old, Root)
        requires (Model(F_Old, Root)[J].K)
        requires (|Model(F_Old, Root)[J].A| == N)
        requires (Model(F, Root)[J].K)
        ensures  (Preserve_Equal(Model(F, Root)[Parent(C(F)[J])].A,
                                Model(F_Old, Root)[Parent(C(F_Old)[J])].A,
                                Model(F, Root)[J].A,
                                Model(F_Old, Root)[J].A,
                                Position(C(F)[J])))
    {
        // For nodes that belong to the tree rooted at Root in the original forest F_Old,
        // and belong to the tree rooted at V in the new forest F:
        // the path in F_Old from Root to the node is the same as the path in F from V to the node,
        // the path in F_Old from Root to the node's parent is the same as the path in F from V to the node's parent,
        // the path in F_Old from Root to the node is the same as the path in F_Old from Root to the node's parent + the node's direction
        // the path in F from Root to the node is the same as the path in F from Root to the node's parent + the node's direction
    } 


    //  procedure Preserve_Equal (S1, S2, S3, S4 : Sequence; D : Direction) with
    //  Ghost,
    //  Global => null,
    //  Pre  => S1 = S2
    //    and then Is_Add (S1, D, S3)
    //    and then Is_Add (S2, D, S4),  
    //  Post => S3 = S4;
    predicate{:verify false} Preserve_Equal(S1: D_Seq, S2: D_Seq, S3: D_Seq, S4: D_Seq, D: Direction)
    {
        (S1 == S2) && (Is_Add(S1, D, S3)) && (Is_Add(S2, D, S4)) ==> (S3 == S4)
    } 


    //  pragma Loop_Invariant
    //              (for all I in 1 .. KI =>
    //                (if Model (F_Old, Root) (I).K and then Last (Model (F_Old, Root) (I).A) <= N then
    //                  (if Model (F, Root) (I).K then Model (F, Root) (I).A = Model (F_Old, Root) (I).A)));
    lemma L_Roots_nodes_same_path2(F: Forest, F_Old: Forest, Root: Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires Valid_Root(F, Root)
        ensures forall N: Index_Type, J: Index_Type, j: Index_Type :: 
                        (0 <= j < J) && 
                        (Model(F_Old, Root)[j].K) && 
                        (|Model(F_Old,Root)[j].A| <= N) ==>
                        (Model(F, Root)[j].K ==> Model(F, Root)[j].A == Model(F_Old, Root)[j].A)
    {
        forall N: Index_Type, J: Index_Type, j: Index_Type 
        {
            if((0 <= j < J) && (Model(F_Old, Root)[j].K) && (|Model(F_Old,Root)[j].A| <= N))
            {
                assert (0 <= j < J) && (Model(F_Old, Root)[j].K) && (|Model(F_Old,Root)[j].A| <= N);
                if(Model(F, Root)[j].K)
                {
                    assert Model(F, Root)[j].K;
                    L_rec_Roots_nodes_same_path2(F, F_Old, Root, N, J, j);
                    assert Model(F, Root)[j].A == Model(F_Old, Root)[j].A;
                    assert Model(F, Root)[j].K ==> Model(F, Root)[j].A == Model(F_Old, Root)[j].A; 
                }
                else
                {
                    assert !Model(F, Root)[j].K;
                    assert Model(F, Root)[j].K ==> Model(F, Root)[j].A == Model(F_Old, Root)[j].A; // false ==> everything
                }
                assert Model(F, Root)[j].K ==> Model(F, Root)[j].A == Model(F_Old, Root)[j].A;
                assert ((0 <= j < J) && (Model(F_Old, Root)[j].K) && (|Model(F_Old,Root)[j].A| <= N)) ==>
                        (Model(F, Root)[j].K ==> Model(F, Root)[j].A == Model(F_Old, Root)[j].A);
            }
            else
            {
                assert !((0 <= j < J) && (Model(F_Old, Root)[j].K) && (|Model(F_Old,Root)[j].A| <= N));
                assert ((0 <= j < J) && (Model(F_Old, Root)[j].K) && (|Model(F_Old,Root)[j].A| <= N)) ==>
                        (Model(F, Root)[j].K ==> Model(F, Root)[j].A == Model(F_Old, Root)[j].A); // false ==> everything
            }
            assert ((0 <= j < J) && (Model(F_Old, Root)[j].K) && (|Model(F_Old,Root)[j].A| <= N)) ==>
                        (Model(F, Root)[j].K ==> Model(F, Root)[j].A == Model(F_Old, Root)[j].A);
        }
        assert forall N: Index_Type, J: Index_Type, j: Index_Type :: 
                            (0 <= j < J) && 
                            (Model(F_Old, Root)[j].K) && 
                            (|Model(F_Old,Root)[j].A| <= N) ==>
                            (Model(F, Root)[j].K ==> Model(F, Root)[j].A == Model(F_Old, Root)[j].A);
    } 

    lemma{:verify false} L_rec_Roots_nodes_same_path2(F: Forest, F_Old: Forest, Root: Index_Type, N: Index_Type, J: Index_Type, j: Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires Valid_Root(F, Root)
        requires 0 <= j < J
        requires Model(F_Old, Root)[j].K
        requires |Model(F_Old,Root)[j].A| <= N
        ensures (Model(F, Root)[j].K ==> Model(F, Root)[j].A == Model(F_Old, Root)[j].A)
    {
        // For nodes that belong to the tree rooted at Root in the original forest F_Old,
        // and belong to the tree rooted at Root in the new forest F:
        // the path in F_Old from Root to the node is the same as the path in F from Root to the node.
        
    } 


    //  pragma Loop_Invariant
    //              (for all I in 1 .. KI =>
    //                (if Model (F_Old, Root) (I).K and then Last (Model (F_Old, Root) (I).A) <= N then
    //                  (if Model (F, V) (I).K then
    //                     Is_Concat (Q => Model (F_Old, Root) (V).A,
    //                                V => Model (F, V) (I).A,
    //                                P => Model (F_Old, Root) (I).A))));
    lemma L_path_concatination2(F: Forest, F_Old: Forest, Root: Index_Type, V: Extended_Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires V != Empty
        requires V != Root
        requires Valid_Root(F, V)
        ensures forall N: Index_Type, J: Index_Type, j: Index_Type :: 
                        (0 <= j < J) &&
                        (Model(F_Old, Root)[j].K && |Model(F_Old, Root)[j].A| <= N - 1) ==>
                        (Model(F, V)[j].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[j].A, Model(F_Old, Root)[j].A))
    {
        forall N: Index_Type, J: Index_Type, j: Index_Type {
            if((0 <= j < J) && (Model(F_Old, Root)[j].K && |Model(F_Old, Root)[j].A| <= N - 1))
            {
                assert (0 <= j < J) && (Model(F_Old, Root)[j].K && |Model(F_Old, Root)[j].A| <= N - 1);
                if(Model(F, V)[j].K){
                    assert Model(F, V)[j].K;
                    L_rec_path_concatination2(F, F_Old, Root, V, N, J, j);
                    assert Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[j].A, Model(F_Old, Root)[j].A);
                    assert Model(F, V)[j].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[j].A, Model(F_Old, Root)[j].A);
                }
                else{
                    assert !(Model(F, V)[j].K);
                    assert Model(F, V)[j].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[j].A, Model(F_Old, Root)[j].A); // false ==> everything
                }
                assert Model(F, V)[j].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[j].A, Model(F_Old, Root)[j].A);
                assert ((0 <= j < J) && (Model(F_Old, Root)[j].K && |Model(F_Old, Root)[j].A| <= N - 1)) ==> 
                    Model(F, V)[j].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[j].A, Model(F_Old, Root)[j].A);
            }
            else
            {
                assert !((0 <= j < J) && (Model(F_Old, Root)[j].K && |Model(F_Old, Root)[j].A| <= N - 1));
                assert (0 <= j < J) && (Model(F_Old, Root)[j].K && |Model(F_Old, Root)[j].A| <= N - 1) ==>
                        (Model(F, V)[j].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[j].A, Model(F_Old, Root)[j].A)); // false ==> everything
            }
            assert (0 <= j < J) && (Model(F_Old, Root)[j].K && |Model(F_Old, Root)[j].A| <= N - 1) ==>
                    (Model(F, V)[j].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[j].A, Model(F_Old, Root)[j].A));
        }
        assert forall N: Index_Type, J: Index_Type, j: Index_Type :: 
                        (0 <= j < J) &&
                        (Model(F_Old, Root)[j].K && |Model(F_Old, Root)[j].A| <= N - 1) ==>
                        (Model(F, V)[j].K ==> Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[j].A, Model(F_Old, Root)[j].A));
    } 


    lemma{:verify false} L_rec_path_concatination2(F: Forest, F_Old: Forest, Root: Index_Type, V: Extended_Index_Type, N: Index_Type, J: Index_Type, j: Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires V != Empty
        requires V != Root
        requires Valid_Root(F, V)
        requires 0 <= j < J
        requires Model(F_Old, Root)[j].K && |Model(F_Old, Root)[j].A| <= N - 1
        requires Model(F, V)[j].K
        ensures Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[j].A, Model(F_Old, Root)[j].A)
    {
        // For nodes that belong the tree rooted at Root in the original forest F_Old,
        // if they belong to the tree rooted at V in the new forest F,
        // then the path from Root to the nodes in F_Old equals to the concatination
        // of the path from Root to V in F_Old, with the path from V to the nodes in F.
    } 
    

    // for R in 1 .. F_Old.S loop
        // if R /= Root and R /= V and F_Old.C (R).Position = Top then
            // Prove_Model_Distinct (F_Old, Root, R);
            // Prove_Model_Preserved (F_Old, F, R);
        // end if;
        // pragma Loop_Invariant
            // (for all P in 1 .. R =>
                // (if P /= Root and P /= V and F_Old.C (P).Position = Top then
                    // Model (F_Old, P) = Model (F, P)));
    lemma L_other_trees(F: Forest, F_Old: Forest, Root: Index_Type, V: Extended_Index_Type)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires V != Empty
        requires V != Root
        requires Valid_Root(F, V)
        ensures forall R: Extended_Index_Type_With_Max, P: Extended_Index_Type_With_Max :: 
                        (0 <= R < S(F_Old)) && (Position(C(F_Old)[R]) == Top) && (R != Root) && (R != V) ==>
                            ((0 <= P <= R) && (Position(C(F_Old)[P]) == Top) && (P != Root) && (P != V) ==>
                                Model(F_Old, P) == Model(F, P))
    {
        forall R: Extended_Index_Type_With_Max, P: Extended_Index_Type_With_Max {
            if ((0 <= R < S(F_Old)) && (Position(C(F_Old)[R]) == Top) && (R != Root) && (R != V)){
                assert (0 <= R < S(F_Old)) && (Position(C(F_Old)[R]) == Top) && (R != Root) && (R != V);
                if((0 <= P <= R) && (Position(C(F_Old)[P]) == Top) && (P != Root) && (P != V)){
                    assert (0 <= P <= R) && (Position(C(F_Old)[P]) == Top) && (P != Root) && (P != V);
                    L_rec_other_trees(F, F_Old, Root, V, R, P);
                    assert Model(F_Old, P) == Model(F, P);
                    assert ((0 <= P <= R) && (Position(C(F_Old)[P]) == Top) && (P != Root) && (P != V) ==>
                                Model(F_Old, P) == Model(F, P));
                }   
                else{
                    assert !((0 <= P <= R) && (Position(C(F_Old)[P]) == Top) && (P != Root) && (P != V));
                    assert ((0 <= P <= R) && (Position(C(F_Old)[P]) == Top) && (P != Root) && (P != V) ==>
                            Model(F_Old, P) == Model(F, P)); //false ==> everything
                }
                assert ((0 <= P <= R) && (Position(C(F_Old)[P]) == Top) && (P != Root) && (P != V) ==>
                            Model(F_Old, P) == Model(F, P));
            }
            else{
                assert !((0 <= R < S(F_Old)) && (Position(C(F_Old)[R]) == Top) && (R != Root) && (R != V));
                assert (0 <= R < S(F_Old)) && (Position(C(F_Old)[R]) == Top) && (R != Root) && (R != V) ==>
                    ((0 <= P <= R) && (Position(C(F_Old)[P]) == Top) && (P != Root) && (P != V) ==>
                        Model(F_Old, P) == Model(F, P)); // false ==> everything
            }
            assert (0 <= R < S(F_Old)) && (Position(C(F_Old)[R]) == Top) && (R != Root) && (R != V) ==>
                ((0 <= P <= R) && (Position(C(F_Old)[P]) == Top) && (P != Root) && (P != V) ==>
                    Model(F_Old, P) == Model(F, P));
        }
        assert forall R: Extended_Index_Type_With_Max, P: Extended_Index_Type_With_Max :: 
                        (0 <= R < S(F_Old)) && (Position(C(F_Old)[R]) == Top) && (R != Root) && (R != V) ==>
                            ((0 <= P <= R) && (Position(C(F_Old)[P]) == Top) && (P != Root) && (P != V) ==>
                                Model(F_Old, P) == Model(F, P));
    } 

    lemma{:verify false} L_rec_other_trees(F: Forest, F_Old: Forest, Root: Index_Type, V: Extended_Index_Type, R: Extended_Index_Type_With_Max, P: Extended_Index_Type_With_Max)
        requires Tree_Structure(F)
        requires Tree_Structure(F_Old)
        requires Valid_Root(F_Old, Root)
        requires V != Empty
        requires V != Root
        requires Valid_Root(F, V)
        requires 0 <= R < S(F_Old)
        requires Position(C(F_Old)[R]) == Top
        requires R != Root
        requires R != V
        requires 0 <= P <= R
        requires Position(C(F_Old)[P]) == Top
        requires P != Root
        requires P != V
        ensures Model(F_Old, P) == Model(F, P)
    {
        // The roots of other trees (not rooted at Root nor at V)
        // have the same trees in the original forest F_Old and the as in the new forest F
        // (same paths from the root to all of the tree nodes)
    } 
                        










// These lemmas are fo the V==Empty case

    lemma Extract_Empty(F: Forest, Root: Index_Type, I: Index_Type, D: Direction, F_Old: Forest, V:Extended_Index_Type)
        requires if D == Left then V == Left_Child(C(F)[I]) else V ==Right_Child(C(F)[I]);
        requires Tree_Structure(F)
        requires Valid_Root(F, Root) && Model(F, Root)[I].K
        requires C(F) != C(F_Old) 
        requires C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old)
        requires V == Empty

        ensures Tree_Structure(F)
        ensures Valid_Root(F, Root)
        ensures V == Peek(F_Old, I, D) && Peek(F, I, D) == Empty
        ensures forall J: Index_Type :: J != V ==> Parent_Of(F, J) == Parent_Of(F_Old, J)
        ensures forall J: Index_Type :: J != V && Parent_Of(F, J) != Empty ==> Position_Of(F, J) == Position_Of(F_Old, J)
        ensures forall J: Index_Type, E: Direction :: J != I || E != D ==> Peek(F, J, E) == Peek(F_Old, J, E)
        ensures forall T: Index_Type :: Valid_Root(F_Old, T) && I != T && V != T ==> Valid_Root(F, T);
        ensures forall T: Index_Type :: Valid_Root(F_Old, T) && Root != T && V != T ==> Model(F, T) == Model(F_Old, T)
        ensures V != Empty ==> Valid_Root(F, V)
        ensures forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> Model(F_Old, Root)[I].K
        ensures forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> 
            Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[I].A, Model(F_Old, Root)[I].A)
        ensures forall I: Index_Type :: Model(F_Old, Root)[I].K ==>
            if V != Empty && Model(F_Old, Root)[V].A <= Model(F_Old, Root)[I].A then Model(F, V)[I].K else Model(F, Root)[I].K
        ensures forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F_Old, Root)[I].K
        ensures forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F, Root)[I].A == Model(F_Old, Root)[I].A
    {
        Extract_Empty_Nodes_Unchanged(F, Root, I, D, F_Old, V);
        Extract_Empty_Trivial(F, Root, I, D, F_Old, V);
        Extract_Empty_Model_Unchanged(F, Root, I, D, F_Old, V);
        Extract_Empty_Same_path(F, Root, I, D, F_Old, V);
        Extract_Empty_Parameters(F, Root, I, D, F_Old, V);
    }
    
    lemma Extract_Empty_Nodes_Unchanged(F: Forest, Root: Index_Type, I: Index_Type, D: Direction, F_Old: Forest, V:Extended_Index_Type)
        requires if D == Left then V == Left_Child(C(F)[I]) else V ==Right_Child(C(F)[I]);
        requires Tree_Structure(F)
        requires C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old)
        requires V == Empty
        ensures forall J: Index_Type :: J != V ==> Parent_Of(F, J) == Parent_Of(F_Old, J)
        ensures forall J: Index_Type :: J != V && Parent_Of(F, J) != Empty ==> Position_Of(F, J) == Position_Of(F_Old, J)
        ensures forall J: Index_Type, E: Direction :: J != I || E != D ==> Peek(F, J, E) == Peek(F_Old, J, E)
        ensures forall T: Index_Type :: Valid_Root(F_Old, T) && I != T && V != T ==> Valid_Root(F, T)
    {}

    lemma Extract_Empty_Trivial(F: Forest, Root: Index_Type, I: Index_Type, D: Direction, F_Old: Forest, V:Extended_Index_Type)
        requires if D == Left then V == Left_Child(C(F)[I]) else V ==Right_Child(C(F)[I]);
        requires V == Empty
        ensures V != Empty ==> Valid_Root(F, V)
        ensures forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> Model(F_Old, Root)[I].K
        ensures forall I: Index_Type :: V != Empty && Model(F, V)[I].K ==> 
            Is_Concat(Model(F_Old, Root)[V].A, Model(F, V)[I].A, Model(F_Old, Root)[I].A)
    {} 

    lemma{:verify false} Extract_Empty_Model_Unchanged(F: Forest, Root: Index_Type, I: Index_Type, D: Direction, F_Old: Forest, V:Extended_Index_Type)
        requires if D == Left then V == Left_Child(C(F)[I]) else V ==Right_Child(C(F)[I]);
        requires Tree_Structure(F)
        requires Valid_Root(F, Root) && Model(F, Root)[I].K
        requires C(F) != C(F_Old) 
        requires C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old)
        requires V == Empty
        ensures forall T: Index_Type :: Valid_Root(F_Old, T) && Root != T && V != T ==> Model(F, T) == Model(F_Old, T)
    {
        // If V is Empty, then the tree's of all roots that does not equal to V or to Root, stay unchanges
    } 

    lemma{:verify false} Extract_Empty_Same_path(F: Forest, Root: Index_Type, I: Index_Type, D: Direction, F_Old: Forest, V:Extended_Index_Type)
        requires if D == Left then V == Left_Child(C(F)[I]) else V ==Right_Child(C(F)[I]);requires if D == Left then V == Left_Child(C(F)[I]) else V ==Right_Child(C(F)[I]);
        requires Tree_Structure(F)
        requires Valid_Root(F, Root) && Model(F, Root)[I].K
        requires C(F) != C(F_Old) 
        requires C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old)
        requires V == Empty
            
        ensures forall I: Index_Type :: Model(F_Old, Root)[I].K ==>
            if V != Empty && Model(F_Old, Root)[V].A <= Model(F_Old, Root)[I].A then Model(F, V)[I].K else Model(F, Root)[I].K
        ensures forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F_Old, Root)[I].K
        ensures forall I: Index_Type :: Model(F, Root)[I].K ==> Model(F, Root)[I].A == Model(F_Old, Root)[I].A
    {
        /* When V is Empty,
            for all nodes I in the tree rooted at Root in the original forest F_Old,
            if V isn't Empty, and the path from Root to V in F_Old is a subpath from Root to I in F_Old,
            then I is in the tree rooted at V in the new forest F (false ==> everything)
            else I is in the tree rooted at Root in the new forest F (since there was no change in the forest) */
        /* When V is Empty,
            all nodes in the tree rooted at Root in the new forest F,
            are in the tree rooted at Root in the original forest F_Old
            (if V is Empty F stayes the same, meaning F represents the exact same forest as F_Old) */
        /* When V is Empty,
            all nodes in the tree rooted at Root in the new forest F,
           the path from Root to the nodes in the original forest F_Old,
           is the same as the path from Root to the nodes in the new forest F.
         */
    }

    lemma Extract_Empty_Parameters(F: Forest, Root: Index_Type, I: Index_Type, D: Direction, F_Old: Forest, V:Extended_Index_Type)

        requires if D == Left then V == Left_Child(C(F)[I]) else V ==Right_Child(C(F)[I]);
        requires Tree_Structure(F)
        requires Valid_Root(F, Root) && Model(F, Root)[I].K
        requires C(F) != C(F_Old) 
        requires C(F)[..] == C(F_Old)[..] && S(F) == S(F_Old)
        requires V == Empty

        ensures Tree_Structure(F)
        ensures Valid_Root(F, Root)
        ensures V == Peek(F_Old, I, D) && Peek(F, I, D) == Empty
    {}
}