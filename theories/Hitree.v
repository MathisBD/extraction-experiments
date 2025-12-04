From Metaprog Require Export Prelude.

(** This file defines (higher-order) interaction trees. *)

(*******************************************************************)
(** * Interaction trees. *)
(*******************************************************************)

(** [hitree E A] is an _interaction tree_: it represents a computation
    with return value in [A] and using the set of effects [E]. *)
Inductive hitree (E : Type -> Type) : Type -> Type :=
| Ret {A} : A -> hitree E A
| Bind {A B} : hitree E A -> (A -> hitree E B) -> hitree E B
| Vis {A} : E A -> hitree E A.

Arguments Ret {E A}.
Arguments Bind {E A B}.
Arguments Vis {E A}.

Notation "t >>= f" := (Bind t f) (right associativity, at level 70).

Definition seq {E A B} (t : hitree E A) (u : hitree E B) : hitree E B :=
  t >>= fun _ => u.

Notation "t >> u" := (seq t u) (right associativity, at level 70).

(** [SubEffect E F], also written [E -< F], means that [E] is a
    sub-effect of [F]: every event [e : E A] can be cast to an event [F A]. *)
Class SubEffect (E F : Type -> Type) := {
  inj_effect : forall A, E A -> F A
}.

Arguments inj_effect {E F _ A}.

Notation "E '-<' F" := (SubEffect E F) (at level 60, no associativity).

Definition trigger {E F A} `{E -< F} (e : E A) : hitree F A :=
  Vis (inj_effect e).

(*******************************************************************)
(** * Concrete effects. *)
(*******************************************************************)

(** Print effect. *)
Variant printE : Type -> Type :=
| Print (s : string) : printE unit.

Definition print {E} `{printE -< E} (s : string) : hitree E unit :=
  trigger (Print s).

(** Failure effect. *)
Variant failE : Type -> Type :=
| Fail {A} (s : string) : failE A.

Definition fail {E A} `{failE -< E} (s : string) : hitree E A :=
  trigger (Fail s).

(** Iteration effect. *)
Variant iterE (E : Type -> Type) : Type -> Type :=
| Iter {A B} (init : A) (step : A -> hitree E (A + B)) : iterE E B.

Arguments Iter {E A B}.

Definition iter {E A B} `{iterE E -< E} (init : A) (step : A -> hitree E (A + B)) : hitree E B :=
  trigger (Iter init step).

(** For loop. *)
Definition for_ {E} `{iterE E -< E} (start stop : nat) (body : nat -> hitree E unit) : hitree E unit :=
  iter start (fun i =>
    if Nat.leb i stop
    then body i >> Ret $ inl (i + 1)
    else Ret $ inr tt).

Notation "'for' i '=' start 'to' stop 'do' body" :=
  (for_ start stop (fun i => body))
  (at level 200, no associativity, i binder).

(** Recursion effect. *)
Variant recE (E : Type -> Type) : Type -> Type :=
| MkFix {A B} (F : nat -> A -> hitree E B) (a : A) : recE E B
| Call {A B} (x : nat) (a : A) : recE E B.

Arguments MkFix {E A B}.
Arguments Call {E A B}.

Definition mkfix {E A B} `{recE E -< E} (F : nat -> A -> hitree E B) (a : A) : hitree E B :=
  trigger (MkFix F a).

Definition call {E A B} `{recE E -< E} (x : nat) (a : A) : hitree E B :=
  trigger (Call x a).

Definition fix_ {E A B} `{recE E -< E} (F : (A -> hitree E B) -> (A -> hitree E B)) (a : A) : hitree E B :=
  mkfix (fun x a => F (call x) a) a.
