Require Import List.
Require Import Arith.
Import ListNotations.

Section SkipList.
Variable A : Type.

Inductive skip_list : Type :=
  | nil : skip_list
  | cons : A -> skip_list -> skip_list
  | skip : nat -> skip_list -> skip_list.
(* I feel evil after writing this definition *)

Fixpoint list2skip_list (l : list A) : skip_list :=
  match l with
  | [] => nil
  | h :: t => cons h (list2skip_list t)
  end.

Fixpoint skip_list2list (s : skip_list) : list A :=
  match s with
  | nil => []
  | cons h t => h :: skip_list2list t
  | skip n l => skipn n (skip_list2list l)
  end.

Theorem skip_list2list_id : forall (l : list A),
  skip_list2list (list2skip_list l) = l.
Proof.
  induction l.
  - trivial.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

End SkipList.


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

Fixpoint list_serialize (l : list nat) : list bool :=
  match l with
  | [] => [false]
  | h :: t => [true] ++ list_serialize t
  end.

Definition deser_skip {T} (orig : skip_list bool) (result : option (T * nat)) : option (T * skip_list bool):=
  match result with
  | None => None
  | Some (a, amt) => Some (a, skip bool amt orig)
  end.

Fixpoint list_deserialize' (bools : skip_list bool) :  option (list A * nat) :=
  match deser_skip bools (deserialize (skip_list2list bool bools)) with
  | None => None
  | Some (n, rest) =>
    match (list_deserialize' rest) with
    | None => None
    | Some (tail, amtRest) => Some (n :: tail, 0)
    end
  end.

Definition list_deserialize (bools : list bool) : option (list A * nat) :=
  list_deserialize' (list2skip_list bools).

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

End ListSerializer.