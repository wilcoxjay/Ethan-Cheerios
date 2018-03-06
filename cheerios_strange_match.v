Require Import List Arith.
Import ListNotations.

Definition serializer (A: Type) := A -> list bool. 
Definition deserializer (A: Type) := list bool -> option (A * list bool).
Definition ser_deser_spec_ (A: Type) (ser : serializer A) (deser : deserializer A) := 
  forall a : A, forall bools: list bool, 
      (deser (ser a ++ bools)) = Some (a, bools).
Class Serializer (A : Type) : Type := {
    serialize : A -> list bool;
    deserialize : list bool -> option (A * list bool);
    ser_deser_identity : forall a : A, forall bools: list bool, 
      (deserialize (serialize a ++ bools)) = Some (a, bools);
}.

Section ListSerializer.
Variable A : Type.
Variable serA : Serializer A.

Definition extract_bools (input : option (list A * list bool)) : list bool :=
  match input with
  | None => [] (* This return value probably doesn't make sense *) 
  | Some (a, bools) => bools
  end.

Fixpoint list_deserialize_strange_match (bools : list bool) :  option (list A * list bool) :=
  match bools with
  | false :: _ => Some ([], 1)
  | true :: bools =>
    match (deserialize bools) with
    | None => None
    | Some (head, bools) =>
      match bools with
      | extract_bools (list_deserialize bools) ++ rest =>
        match (list_deserialize bools) with
        | None => None
        | Some (tail, bools) => Some (head :: tail, bools)
        end
      | _ => None
      end
    | _ => None
    end
  | _ => None
  end.

End ListSerializer.