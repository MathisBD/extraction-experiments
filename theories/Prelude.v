From Stdlib Require Export Bool Nat List.
From Stdlib Require Export PrimString.
From Equations Require Export Equations.

Export PrimString.PStringNotations.
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

(** Ternary version of [sigT]. *)
Inductive sigT3 (A : Type) (P Q R : A -> Type) : Type :=
  existT3 : forall x : A, P x -> Q x -> R x -> sigT3 A P Q R.
Arguments sigT3 [A].
Arguments existT3 [A].

Notation "{ x & P & Q & R }" := (sigT3 (fun x => P) (fun x => Q) (fun x => R))
  (at level 0, x at level 99) : type_scope.

(** Notations to construct sigma-types. *)
Notation "⟨ x , y ⟩" := (existT _ x y).
Notation "⟨ x , y1 , y2 ⟩" := (existT2 _ _ x y1 y2).
Notation "⟨ x , y1 , y2 , y3 ⟩" := (existT3 _ _ _ x y1 y2 y3).
