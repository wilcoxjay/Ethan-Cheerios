(**

## Serialization
Our definition of Serialization includes three things: a serializer,
a deserializer, and a proof of correctness.
*)

Require Import List Arith.
Import ListNotations.

(*begin code*)
(*Variable A:Type.
Definition serialize := A -> list bool.
Definition deserialize := list bool -> option (A * list bool).
Definition deser_ser_spec := forall a : A, forall bools: list bool, 
      (deserialize (serialize a ++ bools)) = Some (a, bools).*)
Class Serializer (A : Type) : Type := {
    serialize : A -> list bool;
    deserialize : list bool -> option (A * list bool);
    deser_ser_identity : forall a : A, forall bools: list bool, 
      (deserialize (serialize a ++ bools)) = Some (a, bools);
}.

(*end code*)
(**
 The serialized form used here is a list of booleans for simplicity,
but this could be replaced with another more sensible structure such
as a stream of bytes. The `option` return type of `deserialize` allows 
for failure in the case of malformed input. The `list bool` is the 
leftover data after deserialization. It is present for sake of composibility.
Without it there would be no way to tell how much of the stream was consumed
in the process of deserialization, and no way to tell where to start
deserializing the next chunk of information. Our identity theorem simply
requires that for any given input serialization and deserialization produces
the same output and consumes no extra information from the stream. Notably, it
does not say anything about malformed streams or that multiple streams could
deserialize to the same result.

To demonstrate this, we will build a simple (inefficient) serializer/deserializer
for `nat`s. The correctness proofs tend to be straightforward and repetitive, but
is included here to show the structure.
*)

(*begin code*)
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

Theorem nat_deser_ser_identity : forall n : nat, forall bools: list bool, 
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
         deser_ser_identity := nat_deser_ser_identity;
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

Theorem pair_deser_ser_identity : forall p : A * B, forall bools: list bool, 
      (pair_deserialize (pair_serialize p ++ bools)) = Some (p, bools).
Proof.
  intros.
  unfold pair_serialize.
  rewrite app_ass.
  unfold pair_deserialize.
  rewrite deser_ser_identity, deser_ser_identity.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.

End PairSerializer.

(** Notice that the information about when to stop deserialization must be encoded
into the stream itself. For example with the following `nat_serialize`, deserialization
of `nat * nat` would become problematic.
*)

Fixpoint nat_serialize_bad (n : nat) : list bool :=
  match n with
  | O => []
  | S n => [true] ++ (nat_serialize n)
  end.

(* This information about the structure of the encoded data is crutial to the well-formedness
of a serializer/deserializer. *)







