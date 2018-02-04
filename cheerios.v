Require Import List.
Require Import Arith.
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

  Fixpoint leaf_insertable (into: tree) (path: list bool): Prop :=
    match into with
    | leaf => 
        match path with
        | [] => True (* Only if the location and tree run out at the same time should we insert *)
        | _ => False
        end
    | stem a l r =>
        match path with
        | [] => False
        | true :: path => (leaf_insertable l path)
        | false :: path => (leaf_insertable r path)
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
    | leaf => 0
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
    (nat_serialize (tree_size t)) ++ (tree_serialize_subtree t []).

  Definition tree_deserialize_node (root :tree) (bools: list bool) : option (tree * list bool) :=
    match (list_deserialize bool BoolSerializer bools) with
    | None => None
    | Some (location, bools) =>
      match (deserialize bools) with
      | None => None
      | Some (a, bools) => Some (tree_insert root (stem a leaf leaf) (rev location), bools)
      end
    end.

  Fixpoint tree_deserialize_impl (remaining : nat) (root : tree) (bools : list bool) : option (tree * list bool) :=
    match remaining with
    | S n =>
      match tree_deserialize_node root bools with
      | None => None
      | Some (root, bools) => tree_deserialize_impl n root bools
      end
    | _ => Some (root, bools)
    end.

  Fixpoint is_subpath (parent path: list bool) : bool := 
    match parent, path with
    | [], _ => true
    | _, [] => false
    | h_parent :: t_parent, h_path :: t_path => (Bool.eqb h_parent h_path) && (is_subpath t_parent t_path)
    end.

  Fixpoint tree_deserialize_subtree (remaining : nat) (root: tree) (path: list bool) (bools: list bool) : option (tree * list bool) :=
    match remaining with
    | S n => 
      match (tree_deserialize_subtree n root path bools) with
      | None => None
      | Some (root, []) => Some (root, bools)
      | Some (root, bools) => 
        match (list_deserialize bool BoolSerializer bools) with
        | None => None
        | Some (location, bools) =>
          match (is_subpath path (rev location)) with
          | false => Some (root, bools)
          | true => 
            match (deserialize bools) with
            | None => None
            | Some (a, bools) => Some (tree_insert root (stem a leaf leaf) (rev location), bools)
            end
          end
        end
      end
    | _ => Some (root, bools)
    end.


  Fixpoint tree_deserialize_size (bools : list bool) : option (nat * list bool):=
    match bools with
    | true :: bools =>
      match tree_deserialize_size bools with
      | Some (n, bools) => Some (S n, bools)
      | None => None
      end
    | false :: bools => Some (0, bools)
    | _ => None
    end.

  Definition tree_deserialize (bools: list bool) : option (tree * list bool) :=
    match nat_deserialize bools with 
    | Some (size, bools) => tree_deserialize_impl size leaf bools
    | None => None
    end.

  Lemma sublocation_child_sublocation: forall location parent sublocation: list bool,
    is_subpath (rev parent) (rev location) = true -> is_subpath (rev parent) (rev (location ++ sublocation)) = true.
  Proof.
    intros location parent sublocation.
    induction sublocation.
    - Admitted.

  Lemma subpath_child_subpath: forall path parent subpath: list bool,
    is_subpath parent path = true -> is_subpath parent (path ++ subpath) = true.
  Proof.
    intros path parent subpath.
    induction parent.
    - simpl. reflexivity.
    - intros. Admitted.
    
Definition placeholder := true.

  Fixpoint skipped_branches (root : tree) (path : list bool) : list tree :=
    match root, path with
    | leaf, _ => [] (* The tree ran out before the path... probably shouldn't happen *)
    | stem a l r, true :: path => r :: (skipped_branches l path) (* The ordering here may have to be flipped *)
    | stem a l r, false :: path => l :: (skipped_branches r path)
    | stem a l r, [] => [] (* Everything underneath will be seen *)
    end.

  Fixpoint unseen_branches_impl (current : tree) (path : list bool) (location: list bool) : list (tree * list bool) :=
    match current, path with
    | leaf, _ => [] (* The tree ran out before the path... probably shouldn't happen *)
    | stem a l r, true :: path => (unseen_branches_impl l path (true::location)) ++ [(r, rev location)] (* The ordering here may have to be flipped *)
    | stem a l r, false :: path => (unseen_branches_impl r path (false::location)) ++ [(l, rev location)]
    | stem a l r, [] => [(stem a l r, location)] (* Everything underneath will be seen *)
    end.

  Definition unseen_branches (root : tree) (path : list bool) : list (tree * list bool) :=
    unseen_branches_impl root path [].

  Fixpoint skipped_branches_clean (current : tree) (path : list bool) : list (tree) :=
    match current, path with
    | leaf, _ => [] (* The tree ran out before the path... probably shouldn't happen *)
    | stem a l r, true :: path => [r] ++ (skipped_branches_clean l path) (* Skpped the right *)
    | stem a l r, false :: path => (skipped_branches_clean r path) (* Already been to the left *)
    | stem a l r, [] => [stem a l r] (* Everything underneath will be seen *)
    end.

  Fixpoint reassemble_tree (root: tree) (path : list bool) (branches: list tree) : tree :=
    match root, path, branches with 
    | stem a l r, [], _ => stem a l r
    | stem a l r, true :: path, [] => stem a l r
    | stem a l r, true :: path, branch :: branches => stem a (reassemble_tree l path branches) branch
    | stem a l r, false :: path, _  => stem a l (reassemble_tree r path branches)
    | leaf, _, _ => leaf
    end.

  Fixpoint seen_tree (root : tree) (path : list bool) (*{struct path}*) : tree :=
    match root, path with
    | leaf, _ => leaf (* The tree ran out before the path... probably shouldn't happen *)
    | stem a l r, true :: path => stem a (seen_tree l path) leaf
    | stem a l r, false :: path => stem a l (seen_tree r path)
    | stem a l r, [] => stem a l r (* Everything underneath will be observed *)
    end.

  Lemma skip_reassemble_whole : forall t : tree, forall path : list bool,
    leaf_insertable t path ->
      reassemble_tree (seen_tree t path) path (skipped_branches_clean t path) = t.
  Proof.
    induction t as [|a l IHL r IHR ]; intros path InTree.
    - simpl. reflexivity.
    - simpl.
      destruct path.
      + trivial.
      + destruct b.
        * simpl. 
          rewrite IHL.
          reflexivity.
          simpl in InTree.
          apply InTree.
  Admitted.

  Lemma tree_insert_at_leaf : forall root : tree, forall path : list bool,
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

  Lemma tree_insert_into_leaf_l : forall root l r: tree, forall path: list bool, forall a: A, 
    leaf_insertable root path -> 
      tree_insert (tree_insert root (stem a leaf r) path) l (path ++ [true]) =
      tree_insert root (stem a l r) path.
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

  Lemma tree_insert_into_leaf_r : forall root r l: tree, forall path: list bool, forall a: A, 
    leaf_insertable root path -> 
      tree_insert (tree_insert root (stem a l leaf) path) r (path ++ [false]) =
      tree_insert root (stem a l r) path.
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

  Lemma tree_insert_into_empty : forall root l r : tree, forall path: list bool, forall a: A, 
    leaf_insertable root path -> 
      tree_insert (
        tree_insert (tree_insert root (stem a leaf leaf) path) l 
          (path ++ [true])) r (path ++ [false]) =
      tree_insert root (stem a l r) path.
  Proof.
    intros.
    rewrite tree_insert_into_leaf_l.
    rewrite tree_insert_into_leaf_r.
    reflexivity.
    apply H.
    apply H.
  Qed.

  Lemma tree_insertable_after_r : forall (root l : tree) (a : A) (path : list bool),
  leaf_insertable root path ->
    leaf_insertable (tree_insert root (stem a l leaf) path) (path ++ [false]).
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

  Lemma tree_insertable_after_l : forall (root r : tree) (a : A) (path : list bool),
  leaf_insertable root path ->
    leaf_insertable (tree_insert root (stem a leaf r) path) (path ++ [true]).
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

  Lemma tree_deser_ser_impl : forall a root : tree, forall location : list bool, forall bs : list bool, forall n : nat,
      leaf_insertable root (rev location) ->
      tree_deserialize_impl (tree_size a + n) root (tree_serialize_subtree a location ++ bs) = 
        tree_deserialize_impl n (tree_insert root a (rev location)) bs.
  induction a as [| a l IHL r IHR]; intros root location bs n InTree.
  - simpl.
    rewrite tree_insert_at_leaf. 
    reflexivity.
    apply InTree.
  - cbn - [tree_insert].
    rewrite !app_ass.
    unfold tree_deserialize_node.
    rewrite list_deser_ser_identity.
    rewrite deser_ser_identity.
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

(* For reassemble
  Lemma tree_deser_ser_partTree : forall seen : tree, forall location bools : list bool,
    leaf_insertable root location ->
      tree_deserialize ((nat_serialize (tree_size root)) ++ ) = Some (root, bools).

  Lemma tree_deser_ser_subtree : forall a r : tree, forall i : list bool, forall bs : list bool, forall n : nat,
      leaf_insertable r (rev i) ->
      tree_deserialize_subtree n r (tree_serialize_subtree a  i ++ bs) = tree_deserialize_subtree n (tree_insert a r (rev i)) bs.
  Proof.
    intros a r i bs n insertable.
    induction a as [|a L IHL R IHR].
    - simpl. reflexivity.
    - unfold tree_serialize_subtree.
      rewrite app_ass, app_ass.
      simpl. *)


  Theorem tree_deser_ser_identity: forall t : tree, forall bools: list bool,
    (tree_deserialize ((tree_serialize t) ++ bools)) = Some (t, bools).
  Proof.
    intros.
    unfold tree_deserialize, tree_serialize.
    rewrite app_ass.
    rewrite nat_deser_ser_identity.
    rewrite (plus_n_O (tree_size t)).
    rewrite tree_deser_ser_impl.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
  Qed.

  Global Instance TreeSerializer : Serializer (tree).
  Proof.
  exact {| serialize := tree_serialize;
           deserialize := tree_deserialize;
           deser_ser_identity := tree_deser_ser_identity;
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

