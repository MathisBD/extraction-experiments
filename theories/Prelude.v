From Stdlib Require Bool Nat List.
From Stdlib Require Export PrimString.

(** Right-associative function application. *)
Notation "f '$' x" := (f x)
  (at level 67, right associativity, only parsing).
