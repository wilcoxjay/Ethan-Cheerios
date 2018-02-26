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
Since this post discusses higher order (JW:right terminology?) types, we need to see how composibility works.
Here, we show serialization for a simple type which requires composibility to implement, the pair.
*)

Module PairSerializer.
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
and does not need to be encoded. Another interesting example are vectors: if you know the type,
you know the length and therefore the shape.

When serialization is performed with the structure up front, the information
about structure comes first in the stream. When deserializating, we can build the structure and then
fill it in as we parse the elements. In the case of a list this information is simply the length. Since
the length is a `nat`, the structure we build is just the right number of recursive calls.

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
Motivate embedded shape
*)

Fixpoint list_serialize_em (l : list nat) : list bool :=
  match l with
  | [] => [false]
  | h :: t => [true] ++ nat_serialize h ++ list_serialize_em t
  end.

(* TODO: How do I "Abort" a fixpoint definition? *)
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

(* No theorem! You can't prove code that won't compile! *)

(*
## Binary Tree Serialization

*)


(* ## Conclusion
Beyond practical necesity, serialization can be used as a forcing function to
understand the information contained within data structures. By requiring a well
defined format, the information contained in that structure may be deduced and formalized.
For example, a list needs to have a length, and a tree needs to have a shape. From there,
the encoding of this information is flexible, although some encodings are easier to work with
than others.
 *)

(* Notes: *)
(* Vocabulary choice: Embedded and up-front. Are there better words to describe this? *)



