

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

property 1: deserialize(serialize(a)) = Some(a, []);

property 2: deserialize(bools) = Some(a, bools') ->
            deserialize(bools ++ bools2) = Some(a, bools' ++ bools2)

*)

Theorem deser_spec_decompose: forall (A : Type) (ser : serializer A) (deser : deserializer A)
    (a: A) (bools leftover other: list bool),
   ((deser (ser a)) = Some(a, [])
/\ ((deser bools) = Some(a, leftover) -> (deser (bools ++ other)) = Some (a, leftover ++ other))) ->
  ser_deser_spec A ser deser.
Proof.
  unfold ser_deser_spec.
  intros A ser deser a bools leftover other props.
  inversion props.
  intros.
  rewrite H0.