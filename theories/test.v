From Stdlib Require Import Extraction PrimString.

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
Extract Constant Nat.pred => "Stdlib.Int.pred".
Extract Constant Nat.add => "Stdlib.Int.add".
Extract Constant Nat.sub => "MyPlugin.Extraction.nat_sub".
Extract Constant Nat.mul => "Stdlib.Int.mul".
Extract Constant Nat.min => "Stdlib.Int.min".
Extract Constant Nat.max => "Stdlib.Int.max".

(** Extraction for primitive strings.
    We don't use [ExtrOCamlPString] because we want to extract [string]
    to [Pstring.t] using an inline directive, so that we don't redefine
    the built-in [string] datatype of OCaml. *)
Extract Inlined Constant PrimString.string => "Pstring.t".
Extract Constant PrimString.max_length => "Pstring.max_length".
Extract Constant PrimString.make => "Pstring.make".
Extract Constant PrimString.length => "Pstring.length".
Extract Constant PrimString.get => "Pstring.get".
Extract Constant PrimString.sub => "Pstring.sub".
Extract Constant PrimString.cat => "Pstring.cat".
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

(*******************************************************************)
(** * Extracting the monad. *)
(*******************************************************************)

Section RunHItree.
  Context (E : Type -> Type).
  Context (ocaml_handle_E : forall A, E A -> A).

  Fixpoint ocaml_run_hitree {A} (t : hitree E A) : (A -> unit) -> unit :=
  match t with
  | Ret x => fun cont => cont x
  | Bind t f => fun cont => ocaml_run_hitree t (fun x => ocaml_run_hitree (f x) cont)
  | Vis e => fun cont => cont (ocaml_handle_E _ e)
  end.

End RunHItree.

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

(*******************************************************************)
(** * Testing. *)
(*******************************************************************)

(** A concrete effect. *)
Inductive E (A : Type) : Type :=
| Wrap : (printE +' failE) A -> E A.

Arguments Wrap {A}.

(** Handle [E] in ocaml. *)
Definition ocaml_handle_E {A} (e : E A) : A :=
  match e with
  | Wrap (sumE_l e) => ocaml_handle_printE e
  | Wrap (sumE_r e) => ocaml_handle_failE e
  end.

Definition print (s : string) : hitree E unit :=
  Vis (Wrap (sumE_l (Print s))).

Definition fail {A} (s : string) : hitree E A :=
  Vis (Wrap (sumE_r (Fail s))).

Definition prg : hitree E unit :=
  print "hello" >> print "world!" >> fail "Program failed: we are done !!".

Definition test : unit :=
  ocaml_run_hitree E (@ocaml_handle_E) prg (fun _ => tt).

Test test.