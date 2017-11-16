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

Lemma nat2bin_identity : forall n: nat,
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
  rewrite nat2bin_identity.
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
    | a :: l => [true] ++ (list_serialize l) ++ serialize a
    end.

  Fixpoint list_deserialize (bools : list bool) : option (list A * list bool) :=
    match bools with
    | false :: bools => Some([], bools)
    | true :: bools =>
      match (list_deserialize bools) with
      | None => None
      | Some (list, bools) =>
        match (deserialize bools) with
        | None => None
        | Some (a, bools) => Some(a :: list, bools)
        end
      end
    | _ => None
    end.

  Lemma list_deser_ser_identity: forall (l : list A) (bools: list bool),
    list_deserialize ((list_serialize l) ++ bools) = Some (l, bools).
  Proof.
    intro l.
    induction l.
    - simpl. reflexivity.
    - simpl.
      intro bools.
      rewrite <- app_assoc.
      rewrite IHl.
      rewrite deser_ser_identity.
      reflexivity.
  Qed.

  Global Instance ListSerializer : Serializer (list A).
  Proof.
  exact {| serialize := list_serialize;
           deserialize := list_deserialize;
           deser_ser_identity := list_deser_ser_identity;
         |}.
  Defined.
End ListSerializer.

Section TreeSerializer.
  Variable A : Type.
  Variable serA : Serializer A.

  Inductive tree: Type := 
  | leaf : tree
  | stem : A -> tree -> tree -> tree.

  Fixpoint tree_insert_default (default: A) (location: Binary) (new into: tree) : tree :=
    match into with
    | leaf => 
        match location with
        | Z => new
        | T b => stem default (tree_insert_default default b new leaf) leaf
        | O b => stem default leaf (tree_insert_default default b new leaf)
        end
    | stem a l r =>
        match location with
        | Z => new
        | T b => stem a (tree_insert_default default b new l) r
        | O b => stem a l (tree_insert_default default b new r)
        end
    end.

  Fixpoint tree_insert (location: Binary) (into: tree) (a:A): tree :=
    match into with
    | leaf => leaf (* not really supported *)
    | stem a l r =>
        match location with
        | Z => stem a leaf leaf
        | T b => stem a (tree_insert b l a) r
        | O b => stem a l (tree_insert b r a)
        end
    end.

  Fixpoint tree_size (t:tree) : nat :=
    match t with
    | leaf => 1
    | stem a l r => 1 + tree_size l + tree_size r
    end.

  Fixpoint tree_serialize_preorder_impl (t: tree) (location: Binary): list bool :=
    match t with
      | leaf => (binary_serialize location) ++ [false]
      | stem a l r => (binary_serialize location) ++ [true] ++ (serialize a) ++
            (tree_serialize_preorder_impl l (T location)) ++ (tree_serialize_preorder_impl r (O location))
    end.

  Definition tree_serialize_preorder (t: tree) : list bool :=
    (nat_serialize (tree_size t)) ++ (tree_serialize_preorder_impl t Z).

  Definition tree_deserialize_one (root:tree) (bools : list bool) : option (tree * list bool) :=
    match (binary_deserialize bools) with
    | None => None
    | Some (location, bools) =>
      match (deserialize bools) with
      | None => None
      | Some (a, bools) => Some (tree_insert location root a , bools)
      end
    end.

  Fixpoint tree_deserialize_preorder_impl (bools : list bool) (root : tree) : option (tree * list bool):=
    match bools with
    | true :: bools =>
      match (tree_deserialize_preorder_impl bools root) with
      | None => None
      | Some (root, bools) => 
        match (binary_deserialize bools) with
        | None => None
        | Some (location, bools) =>
          match (deserialize bools) with
          | Some (a, bools) => Some (tree_insert location root a, bools)
          | None => None
          end
        end
      end
    | false :: bools => Some (root, bools)
    | _ => None
    end.

  Definition tree_deserialize_preorder (bools: list bool) : option (tree * list bool) :=
    tree_deserialize_preorder_impl

  Definition bool_encode_tree (t: tree) :=
    match t with
    | leaf => false
    | stem a l r => true
    end.

  Fixpoint tree_serialize_structure (t : tree) : list bool :=
    match t with
    | leaf => [false]
    | stem a l r => [true; bool_encode_tree l; bool_encode_tree r] ++
       tree_serialize_structure l ++ tree_serialize_structure r
    end.

  Fixpoint tree_serialize_depthfirst (bools : list bool) : option(tree (list bool)) :=
    match bools with 
    | false :: false :: bools => 
    | false :: true :: bools => 

  Fixpoint tree_serialize_depthfirst (t: tree) : list bool :=
    match t with

  Fixpoint tree_deserialize_structure (bools : list bool) : option(tree (list bool)) :=
    match bools with 
    | false :: bools => leaf
    | true :: ls :: rs :: bools => 
      match (tree_deserialize_structure bools) with
    | _ => None
    end.

  Fixpoint tree_serialize (t : tree) : list bool :=
    match t with
    | leaf => [false] 
    | stem a l r => [true] ++ tree_serialize l ++ tree_serialize r ++ serialize a
    end.

  Fixpoint tree_deserialize (bools : list bool) : option (tree * list bool) :=
    match bools with
    | false :: bools => Some (leaf, bools)
    | true :: bools =>
      match (tree_deserialize bools) with
      | None => None
      | Some (l, bools) =>
        match (tree_deserialize bools) with
        | None => None
        | Some (r, bools) =>
          match (deserialize bools) with
          | None => None
          | Some (a, bools) => Some (stem a l r, bools)
          end
        end
      end
    | _ => None
    end.

  Lemma tree_deser_ser_identity: forall (l : list A) (bools: list bool),
    tree_deserialize ((tree_serialize l) ++ bools) = Some (l, bools).
  Proof.
    intro l.
    induction l.
    - simpl. reflexivity.
    - simpl.
      intro bools.
      rewrite <- app_assoc.
      rewrite IHl.
      rewrite deser_ser_identity.
      reflexivity.
  Qed.

  Global Instance TreeSerializer : Serializer (tree A).
  Proof.
  exact {| serialize := list_serialize;
           deserialize := list_deserialize;
           deser_ser_identity := list_deser_ser_identity;
         |}.
  Defined.
End ListSerializer.

Eval compute in deserialize (serialize (true, Z)): option ((bool* Binary) * list bool).

