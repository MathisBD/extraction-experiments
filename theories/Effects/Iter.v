From Metaprog Require Import Prelude Meta.Monad.

(** [iter_step A R] represents the result of a single iteration step
    with an accumulator of type [A] and a result of type [R]. *)
Variant iter_step (A R : Type) : Type :=
| Continue (acc : A)
| Break (res : R).

Arguments Continue {A R}.
Arguments Break {A R}.

(** The effect [iterE] allows one to write (unbounded) loops in meta-programs,
    e.g. for-loops. *)
Variant iterE (E : Type -> Type) : Type -> Type :=
| Iter {A R} (init : A) (step : A -> meta E (iter_step A R)) : iterE E R.

Arguments Iter {E A R}.

(** [iter init step] is a loop with initial accumulator [init] and stepping function [step]. *)
Definition iter {E A R} `{iterE E -< E} (init : A)
    (step : A -> meta E (iter_step A R)) : meta E R :=
  trigger (Iter init step).

(** Continue iterating, with an updated accumulator. *)
Definition continue {E A R} `{iterE E -< E} (acc : A) : meta E (iter_step A R) :=
  ret $ Continue acc.

(** Stop iterating and return the given result. *)
Definition break {E A R} `{iterE E -< E} (res : R) : meta E (iter_step A R) :=
  ret $ Break res.

(** [for_loop start stop body] is a for-loop: it is equivalent to
    [body start >> body (start + 1) >> .. >> body stop]. Note that both bounds are included. *)
Definition for_loop {E} `{iterE E -< E} (start stop : nat) (body : nat -> meta E unit) : meta E unit :=
  iter start (fun i =>
    if Nat.leb i stop then body i >> continue (i + 1) else break tt).

(** For-loop notation on naturals.
    The body is expected to use the functions [continue] and [break]. *)
Notation "'for%' i '=' start 'to' stop 'do' body" :=
  (for_loop start stop (fun i => body))
  (at level 200, no associativity, i binder, only parsing).
