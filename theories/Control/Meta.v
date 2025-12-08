From Metaprog Require Import Prelude Data.Term.

(** This module defines:
    - The meta-programming monad [meta] based on interaction trees.
    - The notion of sub-effect.
    - Common monadic combinators and notations which do not depend on specific effects.

    Specific effects are defined in modules [Effects.XXX]. *)

(** * Meta-programming monad. *)

(** [meta E A] represents a computation with return value in [A]
    and using the set of effects [E]. *)
Inductive meta (E : Type -> Type) : Type -> Type :=
(** [Return a] is a trivial computation which yields a value [a]. *)
| Return {A} : A -> meta E A
(** [Bind t f] executes [t] resulting in a value [a : A], then executes [f a]. *)
| Bind {A B} : meta E A -> (A -> meta E B) -> meta E B
(** [Vis e] triggers an event [e].
    See modules [Effects.XXX] for definitions of specific effects. *)
| Vis {A} : E A -> meta E A.

Arguments Return {E A}.
Arguments Bind {E A B}.
Arguments Vis {E A}.

(** * Sub-effects. *)

(** [SubEffect E F] or [E -< F] means that [E] is a
    sub-effect of [F]: every event [e : E A] can be cast to an event [F A]. *)
Class SubEffect (E F : Type -> Type) := {
  inj_effect : forall A, E A -> F A
}.

Arguments inj_effect {E F _ A}.

Notation "E '-<' F" := (SubEffect E F) (at level 60, no associativity).

Definition trigger {E F A} `{E -< F} (e : E A) : meta F A :=
  Vis (inj_effect e).

(** * Monadic combinators. *)

Definition ret {E A} (a : A) : meta E A := Return a.

(** Infix notation for [Bind]. *)
Notation "t >>= f" := (Bind t f)
  (right associativity, at level 70, only parsing).

(** Let-style notation for [Bind]. *)
Notation "'let%' x ':=' t 'in' f" := (Bind t (fun x => f))
  (right associativity, at level 200, x pattern).

(** [seq t u] or [t >> u] executes [t], discards its result, then executes [u]. *)
Definition seq {E A B} (t : meta E A) (u : meta E B) : meta E B :=
  t >>= fun _ => u.

Notation "t >> u" := (seq t u)
  (right associativity, at level 70).

(** [fmap f t] or [f <$> t] executes [t] and applies [f] to its result. *)
Definition fmap {E A B} (f : A -> B) (t : meta E A) : meta E B :=
  let% x := t in ret (f x).

Notation "f <$> t" := (fmap f t)
  (no associativity, at level 70).

(** [fapply f t] *)
Definition fapply {E A B} (f : meta E (A -> B)) (t : meta E A) : meta E B :=
  let% f' := f in
  let% t' := t in
  ret (f' t').

Notation "f <*> t" := (fapply f t)
  (left associativity, at level 71).

(** [mapM f xs] maps function [f] over the list [xs] and collects the results.
    Effects are sequenced from left to right. *)
Fixpoint mapM {E A B} (f : A -> meta E B) (xs : list A) : meta E (list B) :=
  match xs with
  | [] => ret nil
  | x :: xs =>
    let% y := f x in
    let% ys := mapM f xs in
    ret (y :: ys)
  end.

(** Monadic if-expression. *)
Definition ifM {E A} (cond : meta E bool) (t1 t2 : meta E A) : meta E A :=
  let% b := cond in
  if b then t1 else t2.

(** Notation for monadic if-expressions. *)
Notation "'if%' cond 'then' t1 'else' t2" := (ifM cond t1 t2)
  (at level 200, no associativity).

(** Monadic [and] with the correct short-circuiting behaviour. *)
Definition andM {E} (t1 t2 : meta E bool) : meta E bool :=
  if% t1 then t2 else ret false.

Notation "t1 'and%' t2" := (andM t1 t2)
  (at level 30, right associativity).

(** Monadic [or] with the correct short-circuiting behaviour. *)
Definition orM {E} (t1 t2 : meta E bool) : meta E bool :=
  if% t1 then ret true else t2.

Notation "t1 'or%' t2" := (orM t1 t2)
  (at level 30, right associativity).