Require Import List.
Require Import Arith.
Import ListNotations.

Definition serializer (A: Type) := A -> list bool. 
Definition deserializer (A: Type) := list bool -> option (A * nat).
Definition ser_deser_spec (A: Type) (ser : serializer A) (deser : deserializer A) := 
  forall a : A, forall bools : list bool,
      deser (ser a ++ bools) = Some (a, length (ser a)).

Class Serializer (A : Type) : Type :=
  {
    serialize : A -> list bool;
    deserialize : list bool -> option (A * nat);
    deser_ser_identity : ser_deser_spec A serialize deserialize
  }.

(* I couldn't find a suitable theorem in the coq standard library *)
Theorem skipn_length : forall (A : Type) (l1 l2 : list A),
  skipn (length l1) (l1 ++ l2) = l2.
Proof.
induction l1; intros.
- trivial.
- simpl.
  apply IHl1.
Qed.

Section BoolSerializer.
Definition bool_serialize (b : bool): list bool := [b].

Definition bool_deserialize (bools : list bool): option(bool * nat) := 
  match bools with
  | [] => None
  | h :: t => Some(h, 1)
  end.

Lemma bool_deser_ser_identity : ser_deser_spec bool bool_serialize bool_deserialize.
Proof.
  unfold ser_deser_spec.
  intros.
  simpl.
  reflexivity.
Qed.

Instance BoolSerializer : Serializer bool.
Proof.
exact {| serialize := bool_serialize;
         deserialize := bool_deserialize;
         deser_ser_identity := bool_deser_ser_identity;
       |}.
Defined.
End BoolSerializer.

Section PairSerializer.
Variable A B : Type.
Variable serA : Serializer A.
Variable serB : Serializer B.

Definition pair_serialize (p : A * B) : list bool :=
  serialize (fst p) ++ serialize (snd p).

Definition pair_deserialize (bools : list bool) : option ((A * B) * nat) :=
  match (deserialize bools) with
  | Some (a, amt1) => 
    match (deserialize (skipn amt1 bools)) with
    | Some (b, amt2) => Some( (a, b), amt1 + amt2)
    | None => None
    end
  | None => None
  end.

Theorem pair_ser_deser_identity : 
  ser_deser_spec (A * B) pair_serialize pair_deserialize.
Proof.
  unfold ser_deser_spec.
  intros.
  unfold pair_serialize.
  rewrite app_ass.
  unfold pair_deserialize.
  rewrite deser_ser_identity.
  rewrite skipn_length.
  rewrite deser_ser_identity.
  rewrite <- surjective_pairing.
  rewrite app_length.
  reflexivity.
Qed.

End PairSerializer.

Section NatSerializer.

Fixpoint nat_serialize (n : nat) : list bool :=
  match n with
  | O => [false]
  | S n => [true] ++ (nat_serialize n)
  end.

Fixpoint nat_deserialize (bools : list bool) : option (nat * nat) :=
  match bools with
  | true :: bools => 
    match (nat_deserialize bools) with
    | None => None
  (* Remark: n = remaining + 1 here for this specific deser/ser pair *)
    | Some (n, amt) => Some (S n, S amt)
    end
  | false :: bools => Some (O, 1)
  | [] => None
  end.

Theorem nat_ser_deser_identity :
  ser_deser_spec nat nat_serialize nat_deserialize.
Proof.
  unfold ser_deser_spec.
  induction a; intros.
  - trivial.
  - simpl.
    rewrite IHa.
    reflexivity.
Qed.

End NatSerializer.

Section ListSerializer.
Variable A : Type.
Variable serA : Serializer A.

Fixpoint list_serialize (l : list A) : list bool :=
  match l with
  | [] => [false]
  | h :: t => [true] ++ serialize h ++ list_serialize t
  end.


Fixpoint list_deserialize (bools : list bool) :  option (list A * nat) :=
  match bools with
  | false :: _ => Some ([], 1)
  | true :: bools =>
    match (deserialize bools) with
    | None => None
    | Some (n, amtElem) =>
      match (list_deserialize (skipn amtElem bools)) with
      | None => None
      | Some (tail, amtRest) => Some (n :: tail, amtElem + amtRest)
      end
    end
  | _ => None
  end.


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

End ListSerializer.