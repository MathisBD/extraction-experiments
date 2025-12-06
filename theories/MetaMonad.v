From Metaprog Require Import Prelude Term.

(** This file defines the meta-programming monad [meta] based on interaction trees.
    Specific effects are defined in modules Effect.XXX. *)

(** [meta E A] represents a computation with return value in [A]
    and using the set of effects [E]. *)
Inductive meta (E : Type -> Type) : Type -> Type :=
| Return {A} : A -> meta E A
| Bind {A B} : meta E A -> (A -> meta E B) -> meta E B
| Vis {A} : E A -> meta E A.

Arguments Return {E A}.
Arguments Bind {E A B}.
Arguments Vis {E A}.

Definition ret {E A} (a : A) : meta E A := Return a.

Notation "t >>= f" := (Bind t f)
  (right associativity, at level 70, only parsing).

Notation "'let*' x ':=' t 'in' f" := (Bind t (fun x => f))
  (no associativity, at level 200, x pattern).

(** [seq t u] or [t >> u] executes [t], discards its result, then executes [u]. *)
Definition seq {E A B} (t : meta E A) (u : meta E B) : meta E B :=
  t >>= fun _ => u.

Notation "t >> u" := (seq t u)
  (right associativity, at level 70, only parsing).

(** [fmap f t] or [f <$> t] executes [t] and applies [f] to its result. *)
Definition fmap {E A B} (f : A -> B) (t : meta E A) : meta E B :=
  let* x := t in ret (f x).

Notation "f <$> t" := (fmap f t)
  (no associativity, at level 70, only parsing).

(** [SubEffect E F] or [E -< F] means that [E] is a
    sub-effect of [F]: every event [e : E A] can be cast to an event [F A]. *)
Class SubEffect (E F : Type -> Type) := {
  inj_effect : forall A, E A -> F A
}.

Arguments inj_effect {E F _ A}.

Notation "E '-<' F" := (SubEffect E F) (at level 60, no associativity).

Definition trigger {E F A} `{E -< F} (e : E A) : meta F A :=
  Vis (inj_effect e).