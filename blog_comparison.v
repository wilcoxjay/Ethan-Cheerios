(**
% Encoding Techniques in Verified Serializers
% Ethan Shea and James Wilcox
% March 28, 2018

Serialization can be described as the process of mapping some input data
into a linear arrangement. In practice, this linear arrangement is usually
a list or stream of bytes.

In this post, we will explore different strategies for performing this mapping
and its effects. First our formal notion of serialization will be introduced,
and then we will compare two strategies of laying out the information encoded
in a list and a binary tree.

In particular, the method which information is encoded will be examined. Information
is anything which can be used to describe part of a data structure. For example, in a
graph, the topology and element data are both information which contribute to the data
contained within the whole graph. Information is often tied to a particular layer of
abstraction as represented by a type. In this example, the topology is tied to a
type `graph`, while the element data is tied to some element type `E`. The combination
of the types in the expression `graph E` is tied to all information contained within the
graph. The serialized encoding of this information

Additionally, the `.v` for this post may be found [here]() if you would
like to step through some of the proofs or see omitted details, or write a
serializer of your own.

## Defining Serialization
Our definition of Serialization includes three things: a serializer,
a deserializer, and a proof of correctness.

*)

Require Import List Arith.
Import ListNotations.

(* TODO: How do I use these in my actual definitions? (do I need to for ser/deser?) *)

(*begin code*)
Definition serializer (A: Type) := A -> list bool.

Definition deserializer (A: Type) :=
  list bool -> option (A * list bool).

Definition ser_deser_spec_ A
           (ser : serializer A)
           (deser : deserializer A) :=
  forall (a : A) (bools: list bool),
      (deser (ser a ++ bools)) = Some (a, bools).

Class Serializer (A : Type) : Type := {
    serialize : A -> list bool;
    deserialize : list bool -> option (A * list bool);
    ser_deser_identity : ser_deser_spec_ A serialize deserialize
}.
(*end code*)

(* A trivial boolean serializer for use later *)
Definition bool_serialize (b: bool) := [b].
Definition bool_deserialize (bools: list bool) :=
  match bools with
  | b :: bools => Some (b, bools)
  | [] => None
  end.
Theorem bool_ser_deser_identity:
  ser_deser_spec_ bool bool_serialize bool_deserialize.
Proof.
  unfold ser_deser_spec_.
  trivial.
Qed.

Instance BoolSerializer : Serializer bool.
Proof.
exact {| serialize := bool_serialize;
         deserialize := bool_deserialize;
         ser_deser_identity := bool_ser_deser_identity;
       |}.
Defined.

(**

 The serialized form used here is a list of booleans for simplicity.
[^efficient.] The `option` return type of `deserialize` allows
for failure in the case of malformed input. The `list bool` in the return type is the
leftover data after deserialization. It provides composibility in a similarly to a
state monad. Our identity theorem simply
requires that for any given input, serialization and deserialization produces
the same output and consumes no extra information from the stream. Notably, it
does not say anything about malformed streams or that multiple streams could
deserialize to the same result.

[efficient]: A linked list of booleans is not computationally efficient,
and could be replaced with another more sensible structure such as a stream of bytes.

To demonstrate this, we will build a simple (inefficient) serializer/deserializer
for `nat`s. The correctness proofs tend to be straightforward and repetitive, but
this first one is included here to show the structure.

*)
(*begin code*)
Fixpoint nat_serialize (n : nat) : list bool :=
  match n with
  | O => [false]
  | S n => [true] ++ (nat_serialize n)
  end.

Fixpoint nat_deserialize bools : option (nat * list bool) :=
  match bools with
  | true :: bools => 
    match (nat_deserialize bools) with
    | None => None
    | Some (n, bools) => Some (S n, bools)
    end
  | false :: bools => Some (O, bools)
  | [] => None (* Deserializing an empty stream *)
  end.

Theorem nat_ser_deser_identity :
  ser_deser_spec_ nat nat_serialize nat_deserialize. 
(* Writing Note: I like using this definition because it communicates how the spec is
   defined between a particular ser/deser pair *)
Proof.
(*TODO Is there a way to unfold and rename? It's a shame to use a instead of n in the inductive step. *)
  unfold ser_deser_spec_.
  intros n; induction n; intros.
  - trivial.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.
(*end code*)

Instance NatSerializer : Serializer nat.
Proof.
exact {| serialize := nat_serialize;
         deserialize := nat_deserialize;
         ser_deser_identity := nat_ser_deser_identity;
       |}.
Defined.

(**

Since this post discusses container types, we need to see how composibility works.
Here, we show serialization for a simple type which requires composibility to implement, the pair.
Composibility allows for container types which contain elements of arbitrary type.

*)

Section PairSerializer.
Variable A B : Type.
Variable serA : Serializer A.
Variable serB : Serializer B.

(*begin code*)
Definition pair_serialize (p : A * B) : list bool :=
  serialize (fst p) ++ serialize (snd p).

Definition pair_deserialize bools : option ((A * B) * list bool) :=
  match (deserialize bools) with
  | Some (a, bools) => 
    match (deserialize bools) with
    | Some (b, bools) => Some((a, b), bools)
    | None => None
    end
  | None => None
  end.
(*end code*)

Theorem pair_ser_deser_identity : 
  ser_deser_spec_ (A * B) pair_serialize pair_deserialize.
Proof.
  unfold ser_deser_spec_.
  intros.
  unfold pair_serialize.
  rewrite app_ass.
  unfold pair_deserialize.
  rewrite ser_deser_identity, ser_deser_identity.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.

Instance PairSerializer : Serializer (A * B).
Proof.
exact {| serialize := pair_serialize;
         deserialize := pair_deserialize;
         ser_deser_identity := pair_ser_deser_identity;
       |}.
Defined.

End PairSerializer.

(**

Notice that the information about when to stop deserialization of each element must be encoded
into the stream itself. For example with the following `nat_serialize`, deserialization
of `nat * nat` would become problematic.

*)

(*begin code*)
Fixpoint nat_serialize_broken (n : nat) : list bool :=
  match n with
  | O => []
  | S n => [true] ++ (nat_serialize n)
  end.
(*end code*)

(**

Under this definition, it's unclear what deserializing the `nat * nat` `[true, true true]` should
result in. It could be `(0,3)`, `(1,2)`, `(2,1)` or `(3,0)`. The information about when to stop must be
encoded in the stream itself in one form or another rather than implicitly as the end of the stream.
Consider the serialized `nat * nat` `[true, false,
true, true, false]`. It is unambigiously `(1, 2)`. When deserializing it is known precisely when each `nat`
 finishes, and transitively when the pair finishes. This information about the structure of the encoded
data is crucial to the well-formedness of a serializer/deserializer.

*)

(**

## List Serialization

As data structures become more sophisticated than a pair, they gain more information about their
structure. For a list this information can be observed as its size, and for a binary tree
this might look like its shape. A pair does not have this information because there are
always two elements in a pair. In other words, a pair's shape is always known in advance,
and does not need to be encoded. Another interesting example in this category are vectors:
if you know a vector's type, you know the length and therefore the shape.

When serialization is performed with the structure up front, the information
about structure comes first in the stream. When deserializating, we can build the structure and then
fill it in as we parse the elements. In the case of a list this structure is simply the length
represented as a `nat`.

The encoding is laid out as follows:
[list_front.png]

In code this looks like:


*)
Section ListSerializer.
Variable A: Type.
Variable serA: Serializer A.

(*begin code*)
Fixpoint list_serialize_elts (l : list A) : list bool :=
  match l with
  | [] => []
  | h :: t => serialize h ++ list_serialize_elts t
  end.

Definition list_serialize (l : list A) : list bool :=
  nat_serialize (length l) ++ list_serialize_elts l.


Fixpoint list_deserialize_elts (size : nat) (bools : list bool)
      : option (list A * list bool) :=
  match size with
  | O => Some ([], bools)
  | S size => 
    match (deserialize bools) with
    | None => None
    | Some (n, bools) =>
      match (list_deserialize_elts size bools) with
      | None => None
      | Some (tail, bools) => Some (n :: tail, bools)
      end
    end
  end.

Definition list_deserialize bools :=
  match deserialize bools with
  | None => None
  | Some (size, bools) => list_deserialize_elts size bools
  end.
(*end code*)

Theorem list_ser_deser_identity : 
  ser_deser_spec_ (list A) list_serialize list_deserialize.
Proof.
  unfold ser_deser_spec_.
  intros.
  unfold list_serialize, list_deserialize.
  rewrite app_ass.
  rewrite nat_ser_deser_identity.
  induction a as [|h t]. (* TODO was l, now a *)
  - trivial.
  - simpl.
    rewrite app_ass.
    rewrite ser_deser_identity.
    rewrite IHt.
    reflexivity.
Qed.


Global Instance ListSerializer : Serializer (list A).
Proof.
exact {| serialize := list_serialize;
         deserialize := list_deserialize;
         ser_deser_identity := list_ser_deser_identity;
       |}.
Defined.

(**

An alternitive to putting the structure up front is to embed it with the data. This appears as
follows:

[list_interleaved.png]

There are a couple of advantages to this which relate to when the information about the structure is
known. This structure allows lists of unknown (potentially infinite) size to be serialized. It also
losens the requirement that a structure must be built first in deserialization. This isn't a big deal
for lists, but it can be helpful with more complicated structures.

Let's see what this looks like in code.

*)

(*begin code*)
Fixpoint list_serialize_inter (l : list A) : list bool :=
  match l with
  | [] => [false]
  | h :: t => [true] ++ serialize h ++ list_serialize_inter t
  end.
(*end code*)

(**

Since information about when to stop deserializating is not known until the end, there is no structure
to recurse on. In this way, we conjecture that it's impossible to define this deserialization function
without using general recursion. An attempted definition is given below:
(TODO: Might be a good idea to use more formal terminology here, I wasn't sure how to phrase it)

*)

(*begin code*)
Fail Fixpoint list_deserialize_inter bools :=
  match bools with
  | [] => None
  | false :: bools => Some ([], bools)
  | true :: bools =>
    match nat_deserialize bools with
    | None => None
    | Some (n, bools) =>
      match list_deserialize_em bools with
      | None => None
      | Some (tail, bools) => Some (n :: tail, bools)
      end
    end
  end.
(*end code*)
End ListSerializer.

(**

## Binary Trees

To continue exploring this idea of serializing shape, we neeed to look at a more complicated data
structure such as a binary tree. Our definition of a binary tree is straightforward:

*)

Section Tree.
Variable A : Type.

(*begin code*)
Inductive tree: Type := 
| leaf : tree
| node : A -> tree -> tree -> tree.
(*end code*)
End Tree.
Arguments leaf {_}.
Arguments node {_} _ _ _.

(**

For the interleaved shape tree serializer, the concept of a "path" is needed. A path is simply the list of
directions taken from the root to reach some node. We'll use true to represent left and false to
represent right. Below is the path [true, false].

[path.png]

The only important thing to know about paths is that when recursing into a tree the direction traveled
must be recorded at the end of the list rather than at the start. If right was first in the list, then
it should remain first throughout. In our definitions, this concept is represented as reversing the
breadcrumbs which were appended to the head of the list, after the recursion has finished.

*)

(**

Using the concept of a path, the position and data of any node can be serialized. When this is done for
all nodes in the tree, all information captured by the original data structure has been encoded.

Even though an interleaved structure is impossible to deserialize without general recursion, using an
interleaved structure is still possible if there is just enough information up front to recurse on. The
number of nodes in the tree provides a nice metric.

The encoding using an interleaved structure looks like this:

[tree_interleaved.png]

Serialization is performed as follows:

*)

Section TreeSerializer.
Variable A : Type.
Variable serA : Serializer A.

(*begin code*)
Fixpoint tree_size (t : tree A) : nat :=
  match t with
  | leaf => 0
  | node _ l r => 1 + tree_size l + tree_size r
  end.

Fixpoint tree_insert (into t: tree A) (path: list bool): tree A :=
  match into with
  | leaf => t
  | node a l r =>
      match path with
      | [] => t (* not supported *)
      | true :: path => node a (tree_insert l t path) r
      | false :: path => node a l (tree_insert r t path)
      end
  end.

Fixpoint tree_serialize_subtree_inter (t: tree A) (location: list bool) :=
  match t with
    | leaf => []
    | node a l r => serialize location ++ serialize a
      ++ tree_serialize_subtree_inter l (true :: location)
      ++ tree_serialize_subtree_inter r (false :: location)
  end.

Definition tree_serialize_inter (t: tree A) : list bool :=
  nat_serialize (tree_size t) ++ tree_serialize_subtree_inter t [].
(*end code*)

(**

Deserialization is more complicated. As elements are parsed, they are inserted into the tree structure parsed already.
The insertion function used is not particularly robust, however during deserialization as long as any given node is 
preceded by all of its parents no issues arise. This is the case with a preorder traversal, and also with other
traversals including BFS, so it meets our needs.

*)

(*begin code*)
Fixpoint tree_deserialize_inter_impl
         (remaining : nat) (root : tree A) (bools : list bool)
         : option (tree A * list bool) :=
  match remaining with
  | S n =>
    match deserialize bools with
    | None => None
    | Some (location, bools) =>
      match deserialize bools with
      | None => None
      | Some (a, bools) =>
        tree_deserialize_inter_impl
          n
          (tree_insert root (node a leaf leaf) (rev location))
          bools
      end
    end
  | O => Some (root, bools)
  end.

Definition tree_deserialize_inter bools :=
  match nat_deserialize bools with 
  | Some (size, bools) => tree_deserialize_inter_impl size leaf bools
  | None => None
  end.
(*end code*)

(**

Because of this concept of a path, which is a global address of any particular node, reasoning about a tree
becomes much more difficult. In particular, we must now prove that every insertion is made on a leaf of the
tree so it does not overwrite data or fall off the end.

*)

(*begin code*)
Fixpoint leaf_insertable (into: tree A) (path: list bool): Prop :=
  match into with
  | leaf => 
    (* Only if the location and tree run out at the same time
       should we be able to insert *)
      match path with
      | [] => True
      | _ => False
      end
  | node a l r =>
      match path with
      | [] => False
      | true :: path => (leaf_insertable l path)
      | false :: path => (leaf_insertable r path)
      end
  end.
(*end code*)

Lemma tree_insert_at_leaf : forall root : tree A, forall path : list bool,
  leaf_insertable root path ->
    tree_insert root leaf path = root.
Proof.
  induction root as [| a l IHL r IHR]; intros.
  - destruct path.
    + trivial.
    + simpl in H. inversion H.
  - unfold tree_insert; fold tree_insert.
    destruct path.
    + simpl in H. inversion H.
    + simpl in H.
      destruct b;
        f_equal.
      * apply IHL.
        apply H.
      * apply IHR.
        apply H.
Qed.

Lemma tree_insert_into_leaf_l : forall root l r: tree A, forall path: list bool, forall a: A, 
  leaf_insertable root path -> 
    tree_insert (tree_insert root (node a leaf r) path) l (path ++ [true]) =
    tree_insert root (node a l r) path.
Proof.
  induction root as [| a l IHL r IHR]; intros.
  - destruct path.
    + trivial.
    + simpl in H. inversion H.
  - destruct path; simpl in H.
    + inversion H.
    + destruct b;
      simpl;
      f_equal.
      * apply IHL, H.
      * apply IHR, H.
Qed.

Lemma tree_insert_into_leaf_r : forall root r l: tree A, forall path: list bool, forall a: A, 
  leaf_insertable root path -> 
    tree_insert (tree_insert root (node a l leaf) path) r (path ++ [false]) =
    tree_insert root (node a l r) path.
Proof. (* Is there a way to reuse proof reasoning, like from above? *)
  induction root as [| a l IHL r IHR]; intros.
  - destruct path.
    + trivial.
    + simpl in H. inversion H.
  - destruct path; simpl in H.
    + inversion H.
    + destruct b;
      simpl;
      f_equal.
      * apply IHL, H.
      * apply IHR, H.
Qed.

Lemma tree_insert_into_empty : forall root l r : tree A, forall path: list bool, forall a: A, 
  leaf_insertable root path -> 
    tree_insert (
      tree_insert (tree_insert root (node a leaf leaf) path) l 
        (path ++ [true])) r (path ++ [false]) =
    tree_insert root (node a l r) path.
Proof.
  intros.
  rewrite tree_insert_into_leaf_l.
  rewrite tree_insert_into_leaf_r.
  reflexivity.
  apply H.
  apply H.
Qed.

Lemma tree_insertable_after_r : forall (root l : tree A) (a : A) (path : list bool),
leaf_insertable root path ->
  leaf_insertable (tree_insert root (node a l leaf) path) (path ++ [false]).
Proof.
  induction root as [| a l IHL r IHR]; intros.
  - simpl.
    destruct path.
    + trivial.
    + simpl in H. inversion H.
  - destruct path.
    + simpl in H. inversion H.
    + simpl.
      simpl in H.
      destruct b.
      * apply IHL.
        apply H.
      * apply IHR.
        apply H.
Qed.

Lemma tree_insertable_after_l : forall (root r : tree A) (a : A) (path : list bool),
leaf_insertable root path ->
  leaf_insertable (tree_insert root (node a leaf r) path) (path ++ [true]).
Proof.
  induction root as [| a l IHL r IHR]; intros.
  - simpl.
    destruct path.
    + trivial.
    + simpl in H. inversion H.
  - destruct path.
    + simpl in H. inversion H.
    + simpl.
      simpl in H.
      destruct b.
      * apply IHL.
        apply H.
      * apply IHR.
        apply H.
Qed.

Lemma tree_deser_ser_impl : forall a root : tree A, forall location : list bool, forall bools : list bool, forall n : nat,
    leaf_insertable root (rev location) ->
    tree_deserialize_inter_impl (tree_size a + n) root (tree_serialize_subtree_inter a location ++ bools) = 
      tree_deserialize_inter_impl n (tree_insert root a (rev location)) bools.
Proof.
induction a as [| a l IHL r IHR]; intros root location bools n InTree.
- simpl.
  rewrite tree_insert_at_leaf.
  reflexivity.
  apply InTree.
- cbn - [tree_insert].
  rewrite !app_ass.
  rewrite list_ser_deser_identity.
  rewrite ser_deser_identity.
  rewrite <- plus_assoc.
  rewrite IHL.
  rewrite IHR.
  f_equal.
  rewrite tree_insert_into_empty.
    reflexivity.
  apply InTree.
    rewrite tree_insert_into_leaf_l.
    simpl.
    apply tree_insertable_after_r.
    apply InTree.
    apply InTree.
  apply tree_insertable_after_l.
    apply InTree.
Qed.

Theorem tree_ser_deser_inter_identity: 
  ser_deser_spec_ (tree A) tree_serialize_inter tree_deserialize_inter.
Proof.
  unfold ser_deser_spec_.
  intros t bools.
  unfold tree_deserialize_inter, tree_serialize_inter.
  rewrite app_ass.
  rewrite nat_ser_deser_identity.
  rewrite (plus_n_O (tree_size t)).
  now rewrite tree_deser_ser_impl.
Qed.


Instance TreeInterleavedSerializer : Serializer (tree A).
Proof.
exact {| serialize := tree_serialize_inter;
         deserialize := tree_deserialize_inter;
         ser_deser_identity := tree_ser_deser_inter_identity;
       |}.
Defined.

(**

TODO: use this footnote somewhere. [^tree_efficient]

[tree_efficient]: It's worth noting that this representation could be
made more efficient by recording locations relative to the previous
node instead of absolute ones. However, this fact does not change how
hard it is to reason aboout the tree. Recording relative locations
would allow us to reason about subtrees instead of parts of some tree,
but we still must reason about insertions.

*)

(**

Alternatively, the structure may be recorded at the beginning and then filled in as the tree is parsed.
We must now reason about a tree as both it's shape (`tree unit`) and it's elements
(`list A`).
This technique requires serialization and deserialization to be a two step process, which has the advantage
of better mapping to the information stored in the tree (shape and element data) but also the disadvantage
of being more complicated. 

The shape is encoded with three symbols:
 * [true; true]: The beginning of a `node`
 * [true; false]: The end of a node
 * [false]: A leaf node

Each `node` requieres exactly two subtrees between its start and end marker. The shape is stored as a `tree 
unit`. This works because `unit` contains no information, so `tree unit` only contains the information that
the `tree` portion of `tree A` describes, which is the shape. Since we record this shape in a preorder
traversal, the elements are also encoded in the same order, which makes it easy to marry the two together.

A visual representation of this encoding:
[tree_front.png]

And in code:

*)
(*begin code*)
Fixpoint tree_serialize_shape (t : tree A) : list bool :=
  match t with
  | leaf => [false]
  | node _ l r => [true; true] ++ tree_serialize_shape l ++
                  tree_serialize_shape r ++ [true; false]
  end.

Fixpoint tree_serialize_data_preorder (t : tree A) : list bool :=
  match t with
  | leaf => [] (* No data contained within leaf nodes *)
  | node a l r => serialize a ++ tree_serialize_data_preorder l ++
                  tree_serialize_data_preorder r
  end.

Definition tree_serialize_front (t: tree A) : list bool :=
  tree_serialize_shape t ++ tree_serialize_data_preorder t.

Fixpoint tree_deserialize_shape (bools: list bool) (progress: list (list (tree unit))) : option (tree unit * list bool) :=
  match bools with
  | false :: bools => 
    match progress with
    | [] => Some (leaf, bools)
    | level :: progress => tree_deserialize_shape bools ((leaf :: level) :: progress)
    end
  | true :: true :: bools => tree_deserialize_shape bools ([] :: progress)
  | true :: false :: bools =>
    match progress with
    | [] => None (* End without a beginning *)
    | level :: [] => 
      match level with
      | [r; l] => Some (node tt l r, bools)
      | _ => None
      end
    | level :: parent :: progress =>
      match level with
      | [r; l] => tree_deserialize_shape bools ((node tt l r :: parent) :: progress)
      | _ => None
      end
    end
  | _ => None
  end.

Fixpoint tree_deserialize_front_elts  (shape : tree unit) (bools : list bool) : option (tree A * list bool) :=
  match shape with
  | leaf => Some (leaf, bools)
  | node _ l r =>
    match deserialize bools with
    | None => None
    | Some (a, bools) =>
      match tree_deserialize_front_elts l bools with
      | None => None
      | Some (l, bools) => 
        match tree_deserialize_front_elts r bools with
        | None => None
        | Some (r, bools) => Some (node a l r, bools)
        end
      end
    end
  end.

Definition tree_deserialize_front (bools : list bool) : option (tree A * list bool) :=
  match tree_deserialize_shape bools [] with
  | None => None
  | Some (shape, bools) => tree_deserialize_front_elts shape bools
  end.
(*end code*)

Fixpoint shape_of (t : tree A) : tree unit :=
  match t with
  | leaf => leaf
  | node _ l r => node tt (shape_of l) (shape_of r)
  end.

Lemma tree_shape_ser_deser_aux : forall (a: tree A) (bools: list bool) (level: list (tree unit)) (progress: list (list (tree unit))),
      tree_deserialize_shape (tree_serialize_shape a ++ bools) (level :: progress)
        = tree_deserialize_shape (bools) ((shape_of a :: level) :: progress).
Proof.
  induction a as [| a l IHl r IHr]; intros.
  - reflexivity.
  - unfold tree_deserialize_shape, tree_serialize_shape.
    rewrite !app_ass.
    simpl.
    rewrite IHl.
    rewrite IHr.
    reflexivity.
Qed.

Lemma tree_shape_ser_deser_identity : forall (a: tree A) (bools: list bool),
      tree_deserialize_shape (tree_serialize_shape a ++ bools) [] = Some (shape_of a, bools).
Proof.
  destruct a as [| a l r]; intros.
  - trivial.
  - unfold tree_deserialize_shape, tree_serialize_shape.
    rewrite !app_ass.
    fold tree_deserialize_shape.
    fold tree_serialize_shape.
    simpl.
    rewrite tree_shape_ser_deser_aux.
    rewrite tree_shape_ser_deser_aux.
    simpl.
    reflexivity.
Qed.

Lemma tree_elts_ser_deser_identity : forall (a : tree A) (bools: list bool),
      tree_deserialize_front_elts (shape_of a) (tree_serialize_data_preorder a ++ bools) = Some (a, bools).
Proof.
  induction a as [| a l IHl r IHr]; intros.
  - trivial.
  - unfold tree_deserialize_front_elts, tree_serialize_data_preorder.
    simpl.
    rewrite app_ass.
    rewrite ser_deser_identity.
    rewrite app_ass.
    rewrite IHl.
    rewrite IHr.
    reflexivity.
Qed.

Theorem tree_ser_deser_front_identity :
  ser_deser_spec_ (tree A) tree_serialize_front tree_deserialize_front.
Proof.
  unfold ser_deser_spec_.
  unfold tree_serialize_front, tree_deserialize_front.
  intros.
  rewrite app_ass.
  rewrite tree_shape_ser_deser_identity.
  rewrite tree_elts_ser_deser_identity.
  reflexivity.
Qed.

Instance TreeUpFrontSerializer : Serializer (tree A).
Proof.
exact {| serialize := tree_serialize_front;
         deserialize := tree_deserialize_front;
         ser_deser_identity := tree_ser_deser_front_identity;
       |}.
Defined.

(**

Because of the more recursive nature of the encoding, reasoning is significantly easier. We can consider
any portion of the shape in isolation from all others because there are no ties to any global state. 

*)

(**

Talk about how information dependencies can effect encoding order

*)
(* With cheerios style tree:
Size, elements, shape
vs
shape, elements

second one does not require size because it is known in the shape *)

(**

## Conclusion

Beyond practical necesity, serialization can be used as a forcing function to
understand the information contained within data structures. By requiring a well
defined format, the information contained in that structure may be deduced and formalized.
For example, a list needs to have a length, and a tree needs to have a shape. From there,
the encoding of this information is flexible, although some encodings are easier to work with
than others.

*)

(* Notes: *)
(* Vocabulary choice: Embedded and up-front. Are there better words to describe this? *)



