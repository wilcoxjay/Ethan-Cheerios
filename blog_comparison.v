(**
Serialization can be described as the process of mapping some input data
into a linear arrangement. In practice, this linear arrangement is usually
a list or stream of bytes.

In this post, we will explore different strategies for performing this mapping
and its effects. First our formal notion of serialization will be introduced,
and then we will compare two strategies of laying out the information encoded
in a list and a binary tree.

In addition, the `.v` for this post may be found [here]() if you would
like to step through some of the proofs or see omitted details.

## Defining Serialization
Our definition of Serialization includes three things: a serializer,
a deserializer, and a proof of correctness.
*)

Require Import List Arith.
Import ListNotations.

(*begin code*)
(* TODO: How do I use these in my actual definitions? (do I need to for ser/deser?) *)
Definition serializer (A: Type) := A -> list bool. 
Definition deserializer (A: Type) := list bool -> option (A * list bool).
Definition ser_deser_spec_ (A: Type) (ser : serializer A) (deser : deserializer A) := 
  forall a : A, forall bools: list bool, 
      (deser (ser a ++ bools)) = Some (a, bools).
Class Serializer (A : Type) : Type := {
    serialize : A -> list bool;
    deserialize : list bool -> option (A * list bool);
    ser_deser_identity : forall a : A, forall bools: list bool, 
      (deserialize (serialize a ++ bools)) = Some (a, bools);
}.

(*end code*)
(**
 The serialized form used here is a list of booleans for simplicity.
[^](A linked list of booleans is not computationally efficient, and could be replaced with 
another more sensible structure such as a stream of bytes). The `option` return type of `deserialize` allows
for failure in the case of malformed input. The `list bool` in the return type is the
leftover data after deserialization. It provides composibility in a similarly to a
state monad. Our identity theorem simply
requires that for any given input, serialization and deserialization produces
the same output and consumes no extra information from the stream. Notably, it
does not say anything about malformed streams or that multiple streams could
deserialize to the same result.

To demonstrate this, we will build a simple (inefficient) serializer/deserializer
for `nat`s. The correctness proofs tend to be straightforward and repetitive, but
this first one is included here to show the structure.
*)

(*begin code*)
(*Fixpoint nat_serialize (n : nat) : serializer nat :=*)
Fixpoint nat_serialize (n : nat) : list bool :=
  match n with
  | O => [false]
  | S n => [true] ++ (nat_serialize n)
  end.

Fixpoint nat_deserialize (bools : list bool) : option (nat * list bool) :=
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
   defined between a particular ser/deser pair
 *)
Proof.
(*TODO Is there a way to unfold and rename? It's a shame to use a instead of n in the inductive step. *)
  unfold ser_deser_spec_.
  induction a; intros.
  - trivial.
  - simpl.
    rewrite IHa.
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
Since this post discusses higher order (JW:right terminology? I think it might be higher-kinded) types, we need to see how composibility works.
Here, we show serialization for a simple type which requires composibility to implement, the pair.
*)

Section PairSerializer.
Variable A B : Type.
Variable serA : Serializer A.
Variable serB : Serializer B.

(*begin code*)
Definition pair_serialize (p : A * B) : list bool :=
  serialize (fst p) ++ serialize (snd p).

Definition pair_deserialize (bools : list bool) : option ((A * B) * list bool) :=
  match (deserialize bools) with
  | Some (a, bools) => 
    match (deserialize bools) with
    | Some (b, bools) => Some( (a, b), bools)
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

End PairSerializer.

(** Notice that the information about when to stop deserialization of each element must be encoded
into the stream itself. For example with the following `nat_serialize`, deserialization
of `nat * nat` would become problematic.
*)

Fixpoint nat_serialize_broken (n : nat) : list bool :=
  match n with
  | O => []
  | S n => [true] ++ (nat_serialize n)
  end.

(**
Under this definition, it's unclear what desearialazing the `nat * nat` `[true, true true]` should
result in. It could be `(0,3)`, `(1,2)`, `(2,1)` or `(3,0)`. The information about when to stop must be
encoded in the stream itself in one form or another. Consider the serialized `nat * nat` `[true, false,
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

(*begin code*)
Fixpoint list_serialize_elements (l : list nat) : list bool :=
  match l with
  | [] => []
  | h :: t => nat_serialize h ++ list_serialize_elements t
  end.

Definition list_serialize (l : list nat) : list bool :=
  nat_serialize (length l) ++ list_serialize_elements l.


Fixpoint list_deserialize_elements (size : nat) (bools : list bool) :  option (list nat * list bool) :=
  match size with
  | O => Some ([], bools)
  | S size => 
    match (nat_deserialize bools) with
    | None => None
    | Some (n, bools) =>
      match (list_deserialize_elements size bools) with
      | None => None
      | Some (tail, bools) => Some (n :: tail, bools)
      end
    end
  end.

Definition list_deserialize (bools : list bool) : option (list nat * list bool) :=
  match (nat_deserialize bools) with
  | None => None
  | Some (size, bools) => list_deserialize_elements size bools
  end.
(*end code*)

Theorem list_ser_deser_identity : 
  ser_deser_spec_ (list nat) list_serialize list_deserialize.
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
    rewrite nat_ser_deser_identity. (* Element ser/deser identity *)
    rewrite IHt.
    reflexivity.
Qed.

(**
An alternitive to putting the structure up front is to embed it with the data. This appears as
follows:

[list_embedded.png]

There are a couple of advantages to this which relate to when the information about the structure is
known. This structure allows lists of unknown (potentially infinite) size to be serialized. It also
losens the requirement that a structure must be built first in deserialization. This isn't a big deal
for lists, but it can be helpful with more complicated structures.

Let's see what this looks like in code.

*)

Fixpoint list_serialize_em (l : list nat) : list bool :=
  match l with
  | [] => [false]
  | h :: t => [true] ++ nat_serialize h ++ list_serialize_em t
  end.

(**
Since information about when to stop deserializating is not known until the end, there is no structure
to recurse on. In this way, we conjecture that it's impossible to define this deserialization function
without using general recursion. An attempted definition is given below:
(TODO: Might be a good idea to use more formal terminology here, I wasn't sure how to phrase it)
*)
(* TODO: How do I "Abort" a fixpoint? *)
Fixpoint list_deserialize_em (bools : list bool) :  option (list nat * list bool) :=
  match bools with
  | [] => None
  | false :: bools => Some ([], bools)
  | true :: bools =>
    match (nat_deserialize bools) with
    | None => None
    | Some (n, bools) =>
      match (list_deserialize_em bools) with
      | None => None
      | Some (tail, bools) => Some (n :: tail, bools)
      end
    end
  end.
(*end code*)

(* No theorem! You can't prove code that won't typecheck! *)

(**
## Binary Trees

To continue exploring this idea of serializing shape, we neeed to look at a more complicated data
structure such as a binary tree. Our definition of a binary tree is straightforward:
*)

Section TreeSerializer.
Variable A : Type.
Variable serA : Serializer A.

(*begin code*)
Inductive tree: Type := 
| leaf : tree
| node : A -> tree -> tree -> tree.
(*end code*)

Fixpoint tree_size (t : tree) : nat :=
  match t with
  | leaf => 1
  | node _ l r => 1 + tree_size l + tree_size r
  end.

(**
For the embedded serializer, the concept of a "path" is needed. A path is simply the list of
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

Even though an embedded structure is impossible to deserialize without general recursion, using an
embedded structure is still possible if there is just enough information up front to recurse on. The
number of nodes in the tree provides a nice metric.

The encoding using an embedded structure looks like this:

[tree_embedded.png]

Serialization is performed as follows:

*)

(**
Deserialization is more complicated. As elements are parsed, they are inserted into the existing structure/As elements are parsed their data and path are recorded and then inserted order.
(JW: Does it make sense to deserialize as list bool -> list (path * A) -> tree inserts or skip the list step
and do list bool -> tree inserts? I think the first is easier to reason about and it matches up with the
structure pretty well. On the other hand, the second method involves fewer moving pieces and is more direct.)
The insertion function used is not particularly robust, however as long as any given node is preceded by all
of its parents no issues arise. This is the case with a preorder traversal, and also with a BFS, so it meets
our needs.
*)

(* Code to be filled in later *)

(**
Alternatively, the structure may be recorded at the beginning and then filled in as the tree is parsed.
This technique requires serialization and deserialization to be a two step process, however (something better).

The shape is encoded with two symbols. One signifies a `node` which requires two complete trees, and the other
signifies a leaf which is itself a tree. When no nodes need to be satisfied, then the tree shape is complete.
The shape is stored as a `tree unit`. This works because `unit` contains no information, so `tree unit` only
contains the information that `tree A` describes, which is the shape. Since we record this shape in a preorder
traversal, the elements are also encoded in the same order, which makes it easy to marry the two together.

To make the recursion easier, the same trick of encoding the length will be used. (TODO Is this nececary? It shouldn't be, but I can't find a way to write the shape deserializer without it.)

The structure is encoded as follows:

[tree_upfront.png]

And in code:
*)
(*begin code*)
Fixpoint tree_serialize_shape (t : tree) : list bool :=
  match t with
  | leaf => [false]
  | node _ l r => [true; true] ++ tree_serialize_shape l ++ tree_serialize_shape r ++ [true; false]
  end.

Fixpoint tree_serialize_data_preorder (t : tree) : list bool :=
  match t with
  | leaf => [] (* No data contained within leaf nodes *)
  | node a l r => (serialize a) ++ (tree_serialize_data_preorder l) ++ (tree_serialize_data_preorder r)
  end.

Definition tree_serialize (t: tree) : list bool :=
  tree_serialize_shape t ++ tree_serialize_data_preorder t.

Definition tree_unit := tree.

(* JW: What's the best way to do this? I can't put it in the section because it's assumed that tree = tree A*)
End TreeSerializer.

Fixpoint tree_deserialize_shape (bools: list bool) (progress: list (list (tree unit))) : option (tree unit * list bool) :=
  match bools with
  | false :: bools => 
    match progress with
    | [] => Some (leaf unit, bools)
    | level :: progress => tree_deserialize_shape bools ((leaf unit :: level) :: progress)
    end
  | true :: true :: bools => tree_deserialize_shape bools ([] :: progress)
  | true :: false :: bools =>
    match progress with
    | [] => None (* End without a beginning *)
    | level :: [] => 
      match level with
      | [r; l] => Some (node unit tt l r, bools)
      | _ => None
      end
    | level :: parent :: progress =>
      match level with
      | [r; l] => tree_deserialize_shape bools ((node unit tt l r :: parent) :: progress)
      | _ => None
      end
    end
  | _ => None
  end.

Fixpoint tree_deserialize_elements {A : Type} {serA: Serializer A} (shape : tree unit) (bools : list bool) : option (tree A * list bool) :=
  match shape with
  | leaf _ => Some (leaf A, bools)
  | node _ _ l r =>
    match deserialize bools with
    | None => None
    | Some (a, bools) =>
      match tree_deserialize_elements l bools with
      | None => None
      | Some (l, bools) => 
        match tree_deserialize_elements r bools with
        | None => None
        | Some (r, bools) => Some (node A a l r, bools)
        end
      end
    end
  end.

Definition tree_deserialize {A: Type} {serA: Serializer A} (bools : list bool) : option (tree A * list bool) :=
  match tree_deserialize_shape bools [] with
  | None => None
  | Some (shape, bools) => tree_deserialize_elements shape bools
  end.
(*end code*)

Fixpoint shape_of {A : Type} (t : tree A) : tree unit :=
  match t with
  | leaf _ => leaf unit
  | node _ _ l r => node unit tt (shape_of l) (shape_of r)
  end.

Lemma tree_shape_ser_deser_aux : forall (A : Type) (a: tree A) (bools: list bool) (level: list (tree unit)) (progress: list (list (tree unit))),
      tree_deserialize_shape (tree_serialize_shape A a ++ bools) (level :: progress)
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

Lemma tree_shape_ser_deser_identity : forall (A : Type) (a: tree A) (bools: list bool),
      tree_deserialize_shape (tree_serialize_shape A a ++ bools) [] = Some (shape_of a, bools).
Proof.
  induction a as [| a l IHl r IHr]; intros.
  - trivial.
  - unfold tree_deserialize_shape, tree_serialize_shape.
    rewrite !app_ass.
    fold tree_deserialize_shape.
    fold (tree_serialize_shape A l).
    fold (tree_serialize_shape A r).
    simpl.
    rewrite tree_shape_ser_deser_aux.
    rewrite tree_shape_ser_deser_aux.
    simpl.
    reflexivity.
Qed.

Lemma tree_elements_ser_deser_identity : forall {A : Type} {serA: Serializer A} (a : tree A) (bools: list bool),
      tree_deserialize_elements (shape_of a) (tree_serialize_data_preorder A serA a ++ bools) = Some (a, bools).
Proof.
  induction a as [| a l IHl r IHr]; intros.
  - trivial.
  - unfold tree_deserialize_elements, tree_serialize_data_preorder.
    simpl.
    rewrite app_ass.
    rewrite ser_deser_identity.
    rewrite app_ass.
    rewrite IHl.
    rewrite IHr.
    reflexivity.
Qed.


(* TODO generalize this to A *)
Theorem tree_ser_deser_identity :
  ser_deser_spec_ (tree nat) (tree_serialize nat NatSerializer) (tree_deserialize).
Proof.
  unfold ser_deser_spec_.
  unfold tree_serialize, tree_deserialize.
  intros.
  rewrite app_ass.
  rewrite tree_shape_ser_deser_identity.
  rewrite tree_elements_ser_deser_identity.
  reflexivity.
Qed.


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



