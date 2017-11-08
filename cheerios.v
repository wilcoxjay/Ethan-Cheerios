Require Import List.
Require Import Vector.
Import ListNotations.

Class Serializer (A : Type) : Type :=
  {
    serialize : A -> list bool;
    deserialize : list bool -> option (A * list bool);
    deser_ser_identity : forall a : A, forall bools: list bool, (deserialize ((serialize a) ++ bools)) = Some (a, bools);
  }.

Definition bool_serialize (b : bool): list bool := [b].

Definition bool_deserialize (bools : list bool): option(bool * list bool) := 
  match bools with
  | [] => None
  | h :: t => Some(h, t)
  end.


Lemma bool_deser_ser_identity : forall a : bool, forall bools: list bool,
(bool_deserialize ((bool_serialize a) ++ bools)) = Some (a, bools).
Proof.
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

Inductive Binary : Type :=
  | Z : Binary (* Zero *)
  | T : Binary -> Binary (* Twice *)
  | O : Binary -> Binary (* Twice plus one *)
.

Fixpoint inc (b : Binary) : Binary :=
  match b with
  | Z => O Z
  | T n => O n (* T (O n) *)
  | O n => T (inc n)
  end.

Fixpoint nat2bin (n : nat) : Binary :=
  match n with
  | Datatypes.O => Z
  | S n => inc (nat2bin n)
  end.

Fixpoint bin2nat (b: Binary) : nat :=
  match b with
  | Z => Datatypes.O
  | T b => (bin2nat b) + (bin2nat b)
  | O b => S ((bin2nat b) + (bin2nat b))
  end.

Lemma nat2bin_plus1 : forall n:nat,
  inc (nat2bin n) = nat2bin (S n).
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl.
    reflexivity.
Qed.

Lemma bin2nat_plus1 : forall b:Binary,
  bin2nat (inc b) = S (bin2nat b). 
Proof.
  induction b.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl.
    rewrite IHb.
    rewrite plus_n_Sm.
    rewrite <- plus_Sn_m.
    reflexivity.
Qed.

Lemma nat2bin_invertable : forall n: nat,
  (bin2nat (nat2bin n)) = n.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl.
    rewrite bin2nat_plus1.
    rewrite IHn.
    reflexivity.
Qed.

Lemma bin2nat_invertable : forall b: Binary,
  (nat2bin (bin2nat b)) = b.
Proof.
  intros.
  induction b.
  - simpl. reflexivity.
  - simpl.
    unfold nat2bin.
Abort.

Fixpoint binary_serialize (b : Binary) : list bool :=
  match b with
  | Z => [false]
  | T b => [true; true] ++ (binary_serialize b)
  | O b => [true; false] ++ (binary_serialize b)
  end.

Fixpoint binary_deserialize (bools : list bool) : option (Binary * list bool) :=
  match bools with
  | true :: false :: rest => 
    match (binary_deserialize rest) with
    | None => None
    | Some (b, rest) => Some (O b, rest)
    end
  | true :: true :: rest => 
    match (binary_deserialize rest) with
    | None => None
    | Some (b, rest) => Some (T b, rest)
    end
  | false :: rest => Some (Z, rest)
  | _ => None
  end.

Lemma binary_deser_ser_identity : forall a : Binary, forall bools: list bool,
  (binary_deserialize ((binary_serialize a) ++ bools)) = Some (a, bools).
Proof.
  intros.
  induction a.
  - simpl. 
    reflexivity.
  - simpl.
    rewrite IHa.
    reflexivity.
  - simpl.
    rewrite IHa.
    reflexivity.
Qed.

Instance BinarySerializer : Serializer Binary.
Proof.
exact {| serialize := binary_serialize;
         deserialize := binary_deserialize;
         deser_ser_identity := binary_deser_ser_identity;
       |}.
Defined.

Definition nat_serialize (n : nat) : list bool := binary_serialize (nat2bin n).

Definition nat_deserialize (bools : list bool) : option (nat * list bool) := 
  match (binary_deserialize bools) with
  | None => None
  | Some (b, rest) => Some (bin2nat b, rest)
  end.

Lemma nat_deser_ser_identity: forall a : nat, forall bools: list bool,
  (nat_deserialize ((nat_serialize a) ++ bools)) = Some (a, bools).
Proof.
  intros.
  unfold nat_serialize, nat_deserialize.
  rewrite binary_deser_ser_identity.
  rewrite nat2bin_invertable.
  reflexivity.
Qed.

Section PairSerializer.
  Variable A B : Type.
  Variable serA : Serializer A.
  Variable serB : Serializer B.

  Definition pair_serialize (p : A * B) : list bool :=
    serialize (fst p) ++ serialize (snd p).

  Definition pair_deserialize (bools : list bool) : option ((A * B) * list bool) :=
    match (deserialize bools) with
    | None => None
    | Some (a, bools) => 
      match (deserialize bools) with
      | None => None
      | Some (b, bools) => Some ((a,b), bools)
      end
    end.

  Lemma pair_deser_ser_identity: forall (p : A * B) (bools: list bool),
    pair_deserialize ((pair_serialize p) ++ bools) = Some (p, bools).
  Proof.
    intros.
    unfold pair_serialize, pair_deserialize.
    rewrite <- app_assoc.
    rewrite deser_ser_identity.
    rewrite deser_ser_identity.
    rewrite <- surjective_pairing.
    reflexivity.
  Qed.

  Global Instance PairSerializer : Serializer (A * B).
  Proof.
  exact {| serialize := pair_serialize;
           deserialize := pair_deserialize;
           deser_ser_identity := pair_deser_ser_identity;
         |}.
  Defined.
End PairSerializer.

Section SumSerializer.
  Variable A B : Type.
  Variable serA : Serializer A.
  Variable serB : Serializer B.

  Definition sum_serialize (s : A + B) : list bool :=
    match s with
    | inl a => [true] ++ serialize a
    | inr b => [false] ++ serialize b
    end.

  Definition sum_deserialize (bools : list bool) : option ((A + B) * list bool) :=
    match bools with
    | true :: bools => 
      match (deserialize bools) with
      | Some (a, bools) => Some(inl a, bools)
      | None => None
      end
    | false :: bools => 
      match (deserialize bools) with
      | Some (b, bools) => Some(inr b, bools)
      | None => None
      end
    | _ => None
    end.

  Lemma sum_deser_ser_identity: forall (s: A + B) (bools: list bool),
    sum_deserialize ((sum_serialize s) ++ bools) = Some (s, bools).
  Proof.
    intros.
    destruct s.
    - simpl.
      rewrite deser_ser_identity.
      reflexivity.
    - simpl.
      rewrite deser_ser_identity.
      reflexivity.
  Qed.

  Global Instance SumSerializer : Serializer (A + B).
  Proof.
  exact {| serialize := sum_serialize;
           deserialize := sum_deserialize;
           deser_ser_identity := sum_deser_ser_identity;
         |}.
  Defined.
End SumSerializer.

Section OptionSerializer.
  Variable A : Type.
  Variable serA : Serializer A.

  Definition option_serialize (o : option A) : list bool :=
    match o with
    | Some a => [true] ++ serialize a
    | None => [false]
    end.

  Definition option_deserialize (bools : list bool) : option (option(A) * list bool) :=
    match bools with
    | false :: bools => Some(None, bools)
    | true :: bools => 
      match (deserialize bools) with
      | Some (a, bools) => Some(Some a, bools)
      | None => None
      end
    | _ => None
    end.

  Lemma option_deser_ser_identity: forall (o : option A) (bools: list bool),
    option_deserialize ((option_serialize o) ++ bools) = Some (o, bools).
  Proof.
    intros.
    destruct o.
    - simpl.
      rewrite deser_ser_identity.
      reflexivity.
    - simpl.
      reflexivity.
  Qed.

  Global Instance OptionSerializer : Serializer (option A).
  Proof.
  exact {| serialize := option_serialize;
           deserialize := option_deserialize;
           deser_ser_identity := option_deser_ser_identity;
         |}.
  Defined.
End OptionSerializer.

Section ListSerializer.
  Variable A : Type.
  Variable serA : Serializer A.

  Fixpoint list_serialize (l : list A) : list bool :=
    match l with
    | [] => [false]
    | a :: l => [true] ++ (list_serialize l) ++ serialize a (*[true] ++ serialize a ++ (list_serialize l)*)
    end.

  (* this definition used to fail because coq has no was to know that (deserialize bools) returns an option containing a smaller list *)
  Fixpoint list_deserialize (bools : list bool) : option (list A * list bool) :=
    match bools with
    | false :: bools => Some([], bools)
    | true :: bools =>
      match (list_deserialize bools) with
      | None => None
      | Some (list, bools) =>
        match (deserialize bools) with (* How could we get rid of this triangle code? *)
        | None => None
        | Some (a, bools) => Some(a :: list, bools)
        end
      end
    | _ => None
    end.

  Lemma list_deser_ser_identity: forall (l : list A) (bools: list bool),
    list_deserialize ((list_serialize l) ++ bools) = Some (l, bools).
  Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl.
      rewrite <- app_assoc.
      rewrite IHl.
      rewrite deser_ser_identity.
  Qed.

  Global Instance ListSerializer : Serializer (A * B).
  Proof.
  exact {| serialize := list_serialize;
           deserialize := list_deserialize;
           deser_ser_identity := list_deser_ser_identity;
         |}.
  Defined.
End ListSerializer.



Eval compute in deserialize (serialize (true, Z)): option ((bool* Binary) * list bool).

