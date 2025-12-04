From Stdlib Require Import Nat List Extraction PrimString.

Declare ML Module "extraction-experiments.plugin".

Notation "f '$' x" := (f x) (at level 67, right associativity, only parsing).

Fixpoint list_nth_option {A} (n : nat) (xs : list A) : option A :=
  match xs with
  | nil => None
  | x :: xs =>
    match n with
    | 0 => Some x
    | S n => list_nth_option n xs
    end
  end.

(*******************************************************************)
(** * Extraction for built-in datatypes. *)
(*******************************************************************)

(** Extraction for primitive integers (required to extract primitive strings). *)
From Stdlib Require ExtrOCamlInt63.

(** Extraction for basic datatypes. *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

(** Extract [nat] to primitive integers. *)
Extract Inductive nat => "int" [ "0" "Stdlib.Int.succ" ]
  "MyPlugin.Extraction.nat_elim".
Extract Inlined Constant Nat.pred => "Stdlib.Int.pred".
Extract Inlined Constant Nat.add => "Stdlib.Int.add".
Extract Inlined Constant Nat.sub => "MyPlugin.Extraction.nat_sub".
Extract Inlined Constant Nat.mul => "Stdlib.Int.mul".
Extract Inlined Constant Nat.min => "Stdlib.Int.min".
Extract Inlined Constant Nat.max => "Stdlib.Int.max".
Extract Inlined Constant Nat.leb => "(<=)".
Extract Inlined Constant Nat.ltb => "(<)".

(** Extraction for primitive strings.
    We don't use [ExtrOCamlPString] because we want to extract [string]
    to [Pstring.t] using an inline directive, so that we don't redefine
    the built-in [string] datatype of OCaml. *)
Extract Inlined Constant PrimString.string => "Pstring.t".
Extract Inlined Constant PrimString.max_length => "Pstring.max_length".
Extract Inlined Constant PrimString.make => "Pstring.make".
Extract Inlined Constant PrimString.length => "Pstring.length".
Extract Inlined Constant PrimString.get => "Pstring.get".
Extract Inlined Constant PrimString.sub => "Pstring.sub".
Extract Inlined Constant PrimString.cat => "Pstring.cat".
Extract Constant PrimString.compare =>
  "(fun x y -> let c = Pstring.compare x y in if c = 0 then Eq else if c < 0 then Lt else Gt)".

(*******************************************************************)
(** * Interaction trees. *)
(*******************************************************************)

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

(** Sub-effects. *)
Class SubEffect (E F : Type -> Type) := {
  inj_effect : forall A, E A -> F A
}.

Arguments inj_effect {E F _ A}.

Notation "E '-<' F" := (SubEffect E F) (at level 60, no associativity).

Definition trigger {E F A} `{E -< F} (e : E A) : hitree F A :=
  Vis (inj_effect e).

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

(*******************************************************************)
(** * Extracting the monad. *)
(*******************************************************************)

(** Never ending fuel. *)
Inductive fuel :=
| NoFuel
| OneMoreFuel (f : fuel).

(** We extract [fuel] to [unit]: there is only one fuel [n]
    and it is always of the form [n = OneMoreFuel n].
    This way we can write functions using fuel in Rocq and they never run
    out of fuel in OCaml! *)
Extract Inductive fuel => "unit" [ "()" "(fun _ -> ())" ] "(fun f0 f1 _ -> f1 ())".

(** Ocaml's [Obj.magic]. *)
Parameter ocaml_obj_magic : forall {A B}, A -> B.
Extract Inlined Constant ocaml_obj_magic => "Obj.magic".

(** The effect handler for [Print] in OCaml. *)
Parameter ocaml_handle_Print : string -> unit.
Extract Inlined Constant ocaml_handle_Print => "MyPlugin.Extraction.handle_Print".

(** The effect handler for [Fail] in OCaml. *)
Parameter ocaml_handle_Fail : forall A, string -> A.
Extract Inlined Constant ocaml_handle_Fail => "MyPlugin.Extraction.handle_Fail".

(** Entry for a recursive function. *)
Record entry (E : Type -> Type) := mk_entry {
  entry_dom : Type ;
  entry_codom : Type ;
  entry_fun : entry_dom -> hitree E entry_codom
}.

Arguments entry_dom {E}.
Arguments entry_codom {E}.
Arguments entry_fun {E}.

(*******************************************************************)
(** * Testing. *)
(*******************************************************************)

(** A concrete effect. *)
Inductive E (A : Type) : Type :=
| E_printE (e : printE A)
| E_failE (e : failE A)
| E_iterE (e : iterE E A)
| E_recE (e : recE E A).

Arguments E_printE {A}.
Arguments E_failE {A}.
Arguments E_iterE {A}.
Arguments E_recE {A}.

Instance subeffect_printE : printE -< E := { inj_effect := @E_printE }.
Instance subeffect_failE : failE -< E := { inj_effect := @E_failE }.
Instance subeffect_iterE : iterE E -< E := { inj_effect := @E_iterE }.
Instance subeffect_recE : recE E -< E := { inj_effect := @E_recE }.

(** Run an hitree computation with effect [E]. *)
Fixpoint ocaml_run_hitree {A} (n : fuel) (fs : list (entry E)) (t : hitree E A) : A :=
  match n with NoFuel => ocaml_handle_Fail _ "ocaml_run_hitree: out of fuel (should not happen)" | OneMoreFuel n =>
  match t with
  (* Ret. *)
  | Ret x => x
  (* Bind. *)
  | Bind t f =>
    let x := ocaml_run_hitree n fs t in
    ocaml_run_hitree n fs (f x)
  (* Print effect. *)
  | Vis (E_printE e) =>
    match e with
    | Print s => ocaml_handle_Print s
    end
  (* Failure effect. *)
  | Vis (E_failE e) =>
    match e with
    | Fail s => ocaml_handle_Fail _ s
    end
  (* Iteration effect. *)
  | Vis (E_iterE e) =>
    match e with
    | Iter init step =>
      let ab := ocaml_run_hitree n fs (step init) in
      match ab with
      | inl a => ocaml_run_hitree n fs (Vis $ E_iterE $ Iter a step)
      | inr b => b
      end
    end
  (* Recursion effect. *)
  | Vis (E_recE e) =>
    match e with
    (* MkFix: add the function to the environment and run the body. *)
    | MkFix F a =>
      let x := List.length fs in
      let e := mk_entry E _ _ (F x) in
      ocaml_run_hitree n (fs ++ (e :: nil)) (F x a)
    (* Call: Lookup the function in the environment. *)
    | Call x a =>
      match list_nth_option x fs with
      | Some e => ocaml_run_hitree n fs (ocaml_obj_magic $ entry_fun e $ ocaml_obj_magic a)
      | None => ocaml_handle_Fail _ "In ocaml_run_hitree: [Call] got an unbound function."
      end
    end
  end
  end.

Definition for_ (start stop : nat) (body : nat -> hitree E unit) : hitree E unit :=
  iter start (fun i =>
    if Nat.leb i stop
    then body i >> Ret $ inl (i + 1)
    else Ret $ inr tt).

Definition prg : hitree E unit :=
  for_ 1 5 (fun _ => print "hello") >> print "done".

Definition prg_rec : hitree E unit :=
  let loop := fix_ $ fun loop i =>
    if Nat.ltb i 5 then print "hello" >> loop (i + 1)
    else Ret tt
  in
  loop 1.

Definition test : unit :=
  ocaml_run_hitree NoFuel nil prg_rec.

Test test.