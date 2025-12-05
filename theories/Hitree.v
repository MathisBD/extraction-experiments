From Metaprog Require Import Prelude Term.

(** This file defines (higher-order) interaction trees. *)

(*******************************************************************)
(** * Interaction trees. *)
(*******************************************************************)

(** [hitree E A] is an _interaction tree_: it represents a computation
    with return value in [A] and using the set of effects [E]. *)
Inductive hitree (E : Type -> Type) : Type -> Type :=
| Return {A} : A -> hitree E A
| Bind {A B} : hitree E A -> (A -> hitree E B) -> hitree E B
| Vis {A} : E A -> hitree E A.

Arguments Return {E A}.
Arguments Bind {E A B}.
Arguments Vis {E A}.

Definition ret {E A} (a : A) : hitree E A := Return a.

Notation "t >>= f" := (Bind t f)
  (right associativity, at level 70, only parsing).

Notation "'let*' x ':=' t 'in' f" := (Bind t (fun x => f))
  (no associativity, at level 200, x binder).

Definition seq {E A B} (t : hitree E A) (u : hitree E B) : hitree E B :=
  t >>= fun _ => u.

Notation "t >> u" := (seq t u)
  (right associativity, at level 70, only parsing).

Definition fmap {E A B} (f : A -> B) (t : hitree E A) : hitree E B :=
  let* x := t in ret (f x).

Notation "f <$> t" := (fmap f t)
  (no associativity, at level 70, only parsing).

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
(** * Print effect. *)
(*******************************************************************)

Variant printE : Type -> Type :=
| Print (s : string) : printE unit.

(** [print msg] prints the string [msg]. A newline is automatically inserted
    at the end of the string. *)
Definition print {E} `{printE -< E} (s : string) : hitree E unit :=
  trigger (Print s).

(*******************************************************************)
(** * Failure effect. *)
(*******************************************************************)

Variant failE : Type -> Type :=
| Fail {A} (s : string) : failE A.

(** [fail msg] crashes the program with error message [msg]. *)
Definition fail {E A} `{failE -< E} (s : string) : hitree E A :=
  trigger (Fail s).

(*******************************************************************)
(** * Iteration effect. *)
(*******************************************************************)

(** [iter_step A R] represents the result of a single iteration step
    with an accumulator of type [A] and a result of type [R]. *)
Variant iter_step (A R : Type) : Type :=
(** Continue iterating, with an updated accumulator. *)
| Continue (acc : A)
(** Stop iterating and return the given result. *)
| Break (res : R).

Arguments Continue {A R}.
Arguments Break {A R}.

(** The effect [iterE] allows one to write (unbounded) loops, e.g. for-loops. *)
Variant iterE (E : Type -> Type) : Type -> Type :=
| Iter {A R} (init : A) (step : A -> hitree E (iter_step A R)) : iterE E R.

Arguments Iter {E A R}.

Definition iter {E A R} `{iterE E -< E} (init : A)
    (step : A -> hitree E (iter_step A R)) : hitree E R :=
  trigger (Iter init step).

Definition continue {E A R} `{iterE E -< E} (acc : A) : hitree E (iter_step A R) :=
  ret $ Continue acc.

Definition break {E A R} `{iterE E -< E} (res : R) : hitree E (iter_step A R) :=
  ret $ Break res.

(** [for_ start stop body] is a for-loop: it is equivalent to
    [body start >> body (start + 1) >> .. >> body stop]. Note that both bounds are included. *)
Definition for_ {E} `{iterE E -< E} (start stop : nat) (body : nat -> hitree E unit) : hitree E unit :=
  iter start (fun i =>
    if Nat.leb i stop then body i >> continue (i + 1) else break tt).

(** For-loop notation. The body is expected to use the functions [continue] and [break]. *)
Notation "'for' i '=' start 'to' stop 'do' body" := (for_ start stop (fun i => body))
  (at level 200, no associativity, i binder, only parsing).

(*******************************************************************)
(** * Recursion effect. *)
(*******************************************************************)

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

(** Notation to build a recursive function with one argument. *)
Notation "'letrec' f x ':=' body 'in' cont" := (let f := fix_ (fun f x => body) in cont)
  (at level 200, no associativity, f binder, x binder, only parsing).

(*******************************************************************)
(** * Evar-map effect. *)
(*******************************************************************)

(** [evar_entry] records the information pertaining to an evar: its type
    and optionally its definition. *)
Record evar_entry := {
  evar_type : term ∅ ;
  evar_def : option (term ∅)
}.

(** The effect [evarE] provides access to the evar-map, which stores information
    pertaining to evars. *)
Variant evarE : Type -> Type :=
| FreshEvar : term ∅ -> evarE evar_id
| LookupEvar : evar_id -> evarE (option evar_entry)
| DefineEvar : evar_id -> term ∅ -> evarE unit.

Section EvarOperations.
  Context {E} `{evarE -< E}.

  (** Create a fresh evar with the given type. Returns the id of the new evar. *)
  Definition fresh_evar (ty : term ∅) : hitree E evar_id :=
    trigger (FreshEvar ty).

  (** Lookup the entry associated to an evar. Returns [None] if the evar doesn't exist. *)
  Definition lookup_evar (ev : evar_id) : hitree E (option evar_entry) :=
    trigger (LookupEvar ev).

  (** Get the type of an evar. Returns [None] if the evar doesn't exist. *)
  Definition lookup_evar_type (ev : evar_id) : hitree E (option (term ∅)) :=
    let* entry_opt := lookup_evar ev in
    match entry_opt with
    | Some {| evar_type := ty ; evar_def := _ |} => ret $ Some ty
    | None => ret None
    end.

  (** Get the definition of an evar. Returns [None] if the evar doesn't exist
      of doesn't have a definition. *)
  Definition get_evar_def (ev : evar_id) : hitree E (option (term ∅)) :=
    let* entry_opt := lookup_evar ev in
    match entry_opt with
    | Some {| evar_type := _ ; evar_def := Some def |} => ret $ Some def
    | _ => ret None
    end.

  (** Set the definition of an evar. Fails if the evar is already defined,
      or if the definition doesn't have the correct type. *)
  Definition define_evar (ev : evar_id) (def : term ∅) : hitree E unit :=
    trigger (DefineEvar ev def).

End EvarOperations.