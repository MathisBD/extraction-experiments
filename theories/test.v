From Stdlib Require Import Nat Extraction PrimString.

Declare ML Module "extraction-experiments.plugin".

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

Notation "t >>= f" := (Bind t f) (right associativity, at level 55).

Definition seq {E A B} (t : hitree E A) (u : hitree E B) : hitree E B :=
  t >>= fun _ => u.

Notation "t >> u" := (seq t u) (right associativity, at level 55).

(** Sum of effects. *)
Variant sumE (E1 E2 : Type -> Type) (A : Type) : Type :=
| sumE_l (e : E1 A)
| sumE_r (e : E2 A).

Arguments sumE_l {E1 E2 A}.
Arguments sumE_r {E1 E2 A}.

Notation "E +' F" := (sumE E F) (at level 60, right associativity).

(** Print effect. *)
Variant printE : Type -> Type :=
| Print (s : string) : printE unit.

(** Failure effect. *)
Variant failE : Type -> Type :=
| Fail {A} (s : string) : failE A.

(** Iteration effect. *)
Variant iterE (E : Type -> Type) : Type -> Type :=
| Iter {A B} (init : A) (step : A -> hitree E (A + B)) : iterE E B.

Arguments Iter {E A B}.

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

(*Section RunHItree.
  Context (E : Type -> Type).
  Context (ocaml_handle_E : forall A, E A -> A).

  Fixpoint ocaml_run_hitree {A} (t : hitree E A) : (A -> unit) -> unit :=
    match t with
    | Ret x => fun cont => cont x
    | Bind t f => fun cont => ocaml_run_hitree t (fun x => ocaml_run_hitree (f x) cont)
    | Vis e => fun cont => cont (ocaml_handle_E _ e)
    end.

End RunHItree.*)

(** The effect handler for [Print] in OCaml. *)
Parameter ocaml_handle_Print : string -> unit.
Extract Inlined Constant ocaml_handle_Print => "MyPlugin.Extraction.handle_Print".

Definition ocaml_handle_printE {A} (e : printE A) : A :=
  match e with
  | Print s => ocaml_handle_Print s
  end.

(** The effect handler for [Fail] in OCaml. *)
Parameter ocaml_handle_Fail : forall A, string -> A.
Extract Inlined Constant ocaml_handle_Fail => "MyPlugin.Extraction.handle_Fail".

Definition ocaml_handle_failE {A} (e : failE A) : A :=
  match e with
  | Fail s => ocaml_handle_Fail _ s
  end.

Section HandleIter.
  Context (E : Type -> Type).
  Context (ocaml_handle_hitree : forall A, hitree E A -> (A -> unit) -> unit).

  Fixpoint ocaml_handle_iterE (n : fuel) {A} (e : iterE E A) : (A -> unit) -> unit :=
    match n with NoFuel => (fun _ => tt) | OneMoreFuel n =>
    match e with
    | Iter init step => fun cont =>
      ocaml_handle_hitree _ (step init) (fun ab =>
        match ab with
        | inl a => ocaml_handle_iterE n (Iter a step) cont
        | inr b => cont b
        end)
    end
    end.
End HandleIter.

(*******************************************************************)
(** * Testing. *)
(*******************************************************************)

(** A concrete effect. *)
Inductive E (A : Type) : Type :=
| Wrap : (printE +' failE +' iterE E) A -> E A.

Arguments Wrap {A}.

(** Handle [E] in ocaml. *)
Definition ocaml_handle_E {A} (run_hitree : forall A, hitree E A -> (A -> unit) -> unit)
  (e : E A) : (A -> unit) -> unit :=
  match e with
  | Wrap (sumE_l e) => fun k => k (ocaml_handle_printE e)
  | Wrap (sumE_r (sumE_l e)) => fun k => k (ocaml_handle_failE e)
  | Wrap (sumE_r (sumE_r e)) => fun k => ocaml_handle_iterE E run_hitree NoFuel e k
  end.

Fixpoint ocaml_run_hitree (n : fuel) {A} (t : hitree E A) : (A -> unit) -> unit :=
  match n with NoFuel => (fun _ => tt) | OneMoreFuel n =>
  match t with
  | Ret x => fun k => k x
  | Bind t f => fun k => ocaml_run_hitree n t (fun x => ocaml_run_hitree n (f x) k)
  | Vis e => fun k => ocaml_handle_E (@ocaml_run_hitree n) e k
  end
  end.

Definition print (s : string) : hitree E unit :=
  Vis (Wrap (sumE_l (Print s))).

Definition fail {A} (s : string) : hitree E A :=
  Vis (Wrap (sumE_r (sumE_l (Fail s)))).

Definition iter {A B} (init : A) (step : A -> hitree E (A + B)) : hitree E B :=
  Vis (Wrap (sumE_r (sumE_r (Iter init step)))).

Definition for_ (start stop : nat) (body : nat -> hitree E unit) : hitree E unit :=
  iter start (fun i =>
    if Nat.leb i stop
    then body i >> Ret (inl (i + 1))
    else Ret (inr tt)).

Definition prg : hitree E unit :=
  for_ 1 5 (fun _ => print "hello") >> print "done".

Definition test : unit :=
  ocaml_run_hitree NoFuel prg (fun _ => tt).

Test test.