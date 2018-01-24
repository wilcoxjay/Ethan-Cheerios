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

Fixpoint extract_last (b:Binary) :=
  match b with
  | Z => (Z , Z)
  | T Z => (T Z, Z)
  | O Z => (O Z, Z)
  | T b => (fst (extract_last b), T (snd (extract_last b)))
  | O b => (fst (extract_last b), O (snd (extract_last b)))
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


Instance NatSerializer : Serializer nat.
Proof.
exact {| serialize := nat_serialize;
         deserialize := nat_deserialize;
         deser_ser_identity := nat_deser_ser_identity;
       |}.
Defined.

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

  Lemma list_deser_ser_one: forall (a : A) (l : list A) (bools: list bool),
    list_deserialize ((list_serialize (a :: l)) ++ bools) = 
      Some (a :: list_deserialize ((list_serialize l), bools)).
  Proof.
    intros.
    unfold list_deserialize, list_serialize.
    rewrite app_ass, app_ass.
    simpl.
  Qed.

  Lemma list_deser_ser_one: forall (a : A) (l : list A) (bools: list bool),
    list_deserialize ((list_serialize (a :: l)) ++ bools) = Some (a :: l, bools).
  Proof.
    intros.
    unfold list_deserialize, list_serialize.
    rewrite app_ass, app_ass.
    simpl.
  Qed.

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

  Definition tree_prune (t: tree) :=
    match t with
    | leaf => leaf
    | stem a l r => stem a leaf leaf
    end.

  Fixpoint tree_insert (into node: tree) (path: list bool): tree :=
    match into with
    | leaf => node
    | stem a l r =>
        match path with
        | [] => node (* also not supported *)
        | true :: path => stem a (tree_insert l node path) r
        | false :: path => stem a l (tree_insert r node path)
        end
    end.

  Fixpoint leaf_insertable (into node: tree) (path: list bool): Prop :=
    match into with
    | leaf => 
        match path with
        | [] => True (* Only if the location and tree run out at the same time should we insert *)
        | _ => False
        end
    | stem a l r =>
        match path with
        | [] => False
        | true :: path => (leaf_insertable l node path)
        | false :: path => (leaf_insertable r node path)
        end
    end.

  Fixpoint serialized_fold (fn : tree * list bool -> option(tree * list bool)) (bools : list bool) : option(tree * list bool) :=
    match bools with
    | true :: bools => 
      match (serialized_fold fn bools) with
      | Some (t, bools) => fn (t, bools)
      | None => None
      end
    | false :: bools => Some (leaf, bools)
    | _ => None
    end.

  Fixpoint tree_size (t:tree) : nat :=
    match t with
    | leaf => 1
    | stem a l r => 1 + tree_size l + tree_size r
    end.

  Definition tree_serialize_node (t: tree) (location: list bool): list bool :=
    match t with
      | leaf => []
      | stem a l r => (serialize location) ++ (serialize a)
    end.

  Fixpoint tree_serialize_subtree (t: tree) (location: list bool): list bool :=
    match t with
      | leaf => tree_serialize_node t location
      | stem a l r =>  tree_serialize_node t location  ++ (tree_serialize_subtree l (true :: location)) ++ 
        (tree_serialize_subtree r (false :: location))
    end.

  Fixpoint tree_serialize_header (t : tree) :=
    match t with
    | leaf => []
    | stem a l r => [true] ++ tree_serialize_header l ++ tree_serialize_header r
    end.

  Definition tree_serialize (t: tree) : list bool :=
    (tree_serialize_header t) ++ [false] ++ (tree_serialize_subtree t []).

  Definition tree_deserialize_node (root :tree) (bools: list bool) : option (tree * list bool) :=
    match (list_deserialize bool BoolSerializer bools) with
    | None => None
    | Some (location, bools) =>
      match (deserialize bools) with
      | None => None
      | Some (a, bools) => Some (tree_insert root (stem a leaf leaf) (List.rev location), bools)
      end
    end.

  Fixpoint tree_deserialize_impl (root : tree) (bools : list bool) : option (tree * list bool):=
    match bools with
    | true :: bools =>
      match (tree_deserialize_impl root bools) with
      | None => None
      | Some (root, bools) => tree_deserialize_node root bools
      end
    | false :: bools => Some (root, bools)
    | _ => None
    end.

  Definition tree_deserialize (bools: list bool) : option (tree * list bool) :=
    tree_deserialize_impl leaf bools.
(*    serialized_fold tree_deserialize_node bools. *)
(*
  Theorem tree_deser_ser_one_leaf: forall root : tree, forall bools: list bool, forall location: Binary,
    (tree_deserialize_node root ((tree_serialize_subtree leaf location) ++ bools)) = Some ((tree_insert root leaf location), bools).
  Proof.
    intros.
    unfold tree_deserialize_node, tree_serialize_subtree, tree_serialize_node.
    rewrite app_ass.
    rewrite binary_deser_ser_identity.
    simpl.
    reflexivity.
  Qed.

  Lemma tree_deser_ser_node: forall t root : tree, forall bools: list bool, forall location: Binary,
    (tree_deserialize_node root ((tree_serialize_node t location) ++ bools))
     = Some (tree_insert root (tree_prune t) location, bools).
  Proof.
    intros t root bools.
    unfold tree_deserialize_node.
    destruct t.
    - intros.
      unfold tree_serialize_node.
      rewrite app_ass.
      unfold tree_deserialize_node.
      simpl.
      rewrite binary_deser_ser_identity.
      reflexivity.
    - intros.
      unfold tree_serialize_node.
      rewrite app_ass.
      rewrite binary_deser_ser_identity.
      simpl.
      rewrite deser_ser_identity.
      unfold tree_deserialize_node.
      reflexivity.
  Qed.

  Lemma tree_header_comb: forall t : tree,
    match t with 
    | leaf => tree_serialize_header leaf
    | stem a l r => [true] ++ tree_serialize_header l ++ tree_serialize_header r
    end =
    tree_serialize_header t.
  Proof.
    destruct t.
    - reflexivity.
    - simpl. reflexivity.
  Qed.
*)

  Theorem tree_preorder_deser_ser_identity: forall t : tree, forall bools: list bool,
    (tree_deserialize ((tree_serialize t) ++ bools)) = Some (t, bools).
  Proof.
    intros.
    unfold tree_deserialize, tree_serialize.
    induction t as [|a L IHL R IHR].
    - unfold tree_deserialize_impl, tree_deserialize_node, tree_serialize_header.
      rewrite app_ass, app_ass.
      simpl. 
      reflexivity.
    - (* unfold tree_deserialize_impl, tree_deserialize_node, tree_serialize_header, serialized_fold. *)
      rewrite app_ass, app_ass.
      unfold tree_serialize_header.
      rewrite app_ass, app_ass.
      unfold tree_serialize_subtree.
      simpl. Admitted.

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

  Global Instance TreeSerializer : Serializer (tree).
  Proof.
  exact {| serialize := tree_serialize;
           deserialize := tree_deserialize;
           deser_ser_identity := tree_preorder_deser_ser_identity;
         |}.
  Defined.
End TreeSerializer.

(*Definition test_tree (t : tree nat) : Prop :=
  Some (t, []) = tree_deserialize (tree_serialize t).*)
Check tree nat.
Eval compute in deserialize (serialize 
  (stem nat 1 
    (stem nat 2 (stem nat 3 (leaf nat) (stem nat 4 (leaf nat) (leaf nat))) (leaf nat)) (leaf nat))) : option (tree nat * list bool).

Eval compute in deserialize (serialize (stem nat 2 (stem nat 3 (leaf nat) (stem nat 4 (leaf nat) (leaf nat))) (leaf nat))) : option (tree nat * list bool).

Eval compute in deserialize (serialize (stem nat 0 (leaf nat) (leaf nat))) : option (tree nat * list bool).

Eval compute in deserialize (serialize (leaf nat)) : option (tree nat * list bool).

Eval compute in deserialize (serialize (true, Z)): option ((bool* Binary) * list bool).

