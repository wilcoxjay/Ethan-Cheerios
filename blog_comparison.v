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

## Serialization
Our definition of Serialization includes three things: a serializer,
a deserializer, and a proof of correctness.
*)

Require Import List Arith.
Import ListNotations.

(*begin code*)
Definition serialize_ (A: Type) := A -> list bool. (* TODO: How do I use these in my actual definitions? *)
Definition deserialize_ (A: Type) := list bool -> option (A * list bool).
Definition ser_deser_spec_ (A: Type) (ser : serialize_ A) (deser : deserialize_ A) := 
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
 The serialized form used here is a list of booleans for simplicity,
but this could be replaced with another more sensible structure such
as a stream of bytes. The `option` return type of `deserialize` allows
for failure in the case of malformed input. The `list bool` in the return type is the
leftover data after deserialization. It is present for sake of composability.
Without it there would be no way to tell how much of the stream was consumed
in the process of deserialization, and no way to tell where to start
deserializing the next chunk of information.
Our identity theorem simply
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

Theorem nat_ser_deser_identity : forall n : nat, forall bools: list bool, 
      (nat_deserialize (nat_serialize n ++ bools)) = Some (n, bools).
Proof.
  induction n; intros.
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

(* And now to demonstrate composibility, we will implement a serializer/deserializer
for a pair.
*)

Module PairSerializer.
Variable A B : Type.
Variable serA : Serializer A.
Variable serB : Serializer B.

(*begin code*)
(*Definition pair_serialize ((a,b) : A * B) : list bool :=
  serialize a ++ serialize b.*)
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

Theorem pair_ser_deser_identity : forall p : A * B, forall bools: list bool, 
      (pair_deserialize (pair_serialize p ++ bools)) = Some (p, bools).
Proof.
  intros.
  unfold pair_serialize.
  rewrite app_ass.
  unfold pair_deserialize.
  rewrite ser_deser_identity, ser_deser_identity.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.

End PairSerializer.

(** Notice that the information about when to stop deserialization must be encoded
into the stream itself. For example with the following `nat_serialize`, deserialization
of `nat * nat` would become problematic.
*)

Fixpoint nat_serialize_broken (n : nat) : list bool :=
  match n with
  | O => []
  | S n => [true] ++ (nat_serialize n)
  end.

(* This information about the structure of the encoded data is crucial to the well-formedness
of a serializer/deserializer.
 *)

(*
## List Serialization

As data structures become more sophisticated than a pair, they gain information about their
structure. For a list this information can be observed as its size, and for a binary tree
this might look like its shape. A pair does not have this information because there are
always two elements in a pair. In other words, a pair's shape is always known in advance,
and does not need to be encoded.

When serialization is performed with the structure up front, we can put all the information
about structure at the beginning of the stream and then fill in the structure as we parse the
data for the elements. For a list this information is simply the length. It can be encoded
before all the elements as shown:

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

Theorem list_ser_deser_identity : forall l : list nat, forall bools: list bool, 
      (list_deserialize (list_serialize l ++ bools)) = Some (l, bools).
Proof.
  intros.
  unfold list_serialize, list_deserialize.
  rewrite app_ass.
  rewrite nat_ser_deser_identity.
  induction l as [|h t].
  - trivial.
  - simpl.
    rewrite app_ass.
    rewrite nat_ser_deser_identity. (* Element ser/deser identity *)
    rewrite IHt.
    reflexivity.
Qed.

(*
## Embedded Structure Serialization

*)





