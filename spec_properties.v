

Require Import List Arith.
Import ListNotations.

Definition serializer (A: Type) := A -> list bool.

Definition deserializer (A: Type) :=
  list bool -> option (A * list bool).

Definition ser_deser_spec A
           (ser : serializer A)
           (deser : deserializer A) :=
  forall (a : A) (bools: list bool),
      (deser (ser a ++ bools)) = Some (a, bools).

(*

property 1: forall a, deserialize(serialize(a)) = Some(a, []);

property 2: forall bools...,
            deserialize(bools) = Some(a, bools') ->
            deserialize(bools ++ bools2) = Some(a, bools' ++ bools2)

*)

Theorem deser_spec_decompose :
  forall (A : Type) (ser : serializer A) (deser : deserializer A),
    (forall a, deser (ser a) = Some (a, [])) ->
    (forall a (bools leftover other: list bool),
        deser bools = Some (a, leftover) ->
        deser (bools ++ other) = Some (a, leftover ++ other)) ->
    ser_deser_spec A ser deser.
Proof.
  unfold ser_deser_spec.
  intros A ser deser P1 P2 a bools.
  now erewrite P2 by auto.
Qed.