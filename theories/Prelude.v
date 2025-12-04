From Stdlib Require Bool Nat List.
From Stdlib Require Export PrimString.
From Equations Require Export Equations.
Export List.ListNotations.

(** Right-associative function application. *)
Notation "f '$' x" := (f x)
  (at level 67, right associativity, only parsing).

(** Compute the sum of a list of naturals.
    Returns [0] if the list is empty. *)
Equations sum : list nat -> nat :=
sum [] := 0 ;
sum (x :: xs) := x + sum xs.

Equations option_apply {A B} : option (A -> B) -> option A -> option B :=
option_apply (Some f) (Some x) := Some (f x) ;
option_apply _ _ := None.

Equations option_sequence {A} : list (option A) -> option (list A) :=
option_sequence [] := Some nil ;
option_sequence (None :: _) := None ;
option_sequence (Some x :: xs) := option_map (cons x) (option_sequence xs).
