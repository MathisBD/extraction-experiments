From Metaprog Require Import Prelude.

(** This module defines:
    - The meta-programming monad [meta] based on interaction trees.
    - The notion of sub-effect.
    - Common monadic combinators and notations which do not depend on specific effects.

    Specific effects are defined in modules [Effects.XXX]. *)

(***********************************************************************)
(** * Meta-programming monad. *)
(***********************************************************************)

(** [meta E A] represents a computation with return value in [A]
    and using the set of effects [E]. *)
Inductive meta (E : Type -> Type) : Type -> Type :=
(** [Ret a] is a trivial computation which yields a value [a]. *)
| Ret {A} : A -> meta E A
(** [Bind t f] executes [t] resulting in a value [a : A], then executes [f a]. *)
| Bind {A B} : meta E A -> (A -> meta E B) -> meta E B
(** [Vis e] triggers an event [e].
    See modules [Effects.XXX] for definitions of specific effects. *)
| Vis {A} : E A -> meta E A.

Arguments Ret {E A}.
Arguments Bind {E A B}.
Arguments Vis {E A}.

(***********************************************************************)
(** * Sum of effects. *)
(***********************************************************************)

Variant sumE (E F : Type -> Type) : Type -> Type :=
| sumE_l A : E A -> sumE E F A
| sumE_r A : F A -> sumE E F A.

Arguments sumE_l {E F A}.
Arguments sumE_r {E F A}.

Notation "E '+'' F" := (sumE E F) (at level 30, right associativity).

(***********************************************************************)
(** * Sub-effects. *)
(***********************************************************************)

(** [subeffect E F] or [E -< F] means that [E] is a sub-effect of [F]:
    every event [e : E A] can be cast to an event [F A]. *)
Class subeffect (E F : Type -> Type) : Type := {
  inj_event : forall A, E A -> F A
}.

Arguments inj_event {E F _ A}.

Notation "E '-<' F" := (subeffect E F) (at level 60, no associativity).

Definition trigger {E F A} `{E -< F} (e : E A) : meta F A :=
  Vis (inj_event e).

(** We setup typeclass search for [subeffect] such that the search can't loop:
    instead of declaring a transitivity instance we bake transitivity
    inside specific rules e.g. [subeffect_sum_l]. *)

#[export] Instance subeffect_refl E : E -< E := {|
  inj_event _ e := e
|}.

#[export] Instance subeffect_sum_l E F1 F2 (H : E -< F1) : E -< F1 +' F2 := {|
  inj_event _ e := sumE_l (inj_event e)
|}.

#[export] Instance subeffect_sum_r E F1 F2 (H : E -< F2) : E -< F1 +' F2 := {|
  inj_event _ e := sumE_r (inj_event e)
|}.

(***********************************************************************)
(** * Monadic combinators. *)
(***********************************************************************)

Definition ret {E A} (a : A) : meta E A := Ret a.

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