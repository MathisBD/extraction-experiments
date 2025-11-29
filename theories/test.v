From Stdlib Require Import List Extraction PrimString.
Import ListNotations.

Declare ML Module "extraction-experiments.plugin".

(*******************************************************************)
(** * Setup extraction. *)
(*******************************************************************)

(** Extraction for primitive integers (required to extract primitive strings). *)
From Stdlib Require ExtrOCamlInt63.

(** Extraction for basic datatypes. *)
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive list => "list" [ "[]" "(::)" ].

(** Extraction for primitive strings. *)
Extract Inlined Constant PrimString.string => "Pstring.t".
Extract Constant PrimString.max_length => "Pstring.max_length".
Extract Constant PrimString.make => "Pstring.make".
Extract Constant PrimString.length => "Pstring.length".
Extract Constant PrimString.get => "Pstring.get".
Extract Constant PrimString.sub => "Pstring.sub".
Extract Constant PrimString.cat => "Pstring.cat".
Extract Constant PrimString.compare => "(fun x y -> let c = Pstring.compare x y in if c = 0 then Eq else if c < 0 then Lt else Gt)".

(*******************************************************************)
(** * Extracting the monad. *)
(*******************************************************************)

(** The effect handler for [Print] is written in OCaml. *)
Parameter ocaml_handle_print : string -> unit.
Extract Inlined Constant ocaml_handle_print => "MyPlugin.Extraction_interface.ocaml_handle_print".

(** The monad. *)
Inductive M : Type -> Type :=
| Ret {A} : A -> M A
| Bind {A B} : M A -> (A -> M B) -> M B
| Print : string -> M unit.

Notation "t >>= f" := (Bind t f) (right associativity, at level 55).

Definition seq {A B} (t : M A) (u : M B) :=
  t >>= fun _ => u.

Notation "t >> u" := (seq t u) (right associativity, at level 55).

Fixpoint eval_M {A} (t : M A) : (A -> unit) -> unit :=
  match t with
  | Ret x => fun cont => cont x
  | Bind t f => fun cont => eval_M t (fun x => eval_M (f x) cont)
  | Print str => fun cont => cont (ocaml_handle_print str)
  end.

(*******************************************************************)
(** * Testing. *)
(*******************************************************************)

Definition prg :=
  Print "hello" >> Print "there" >> Print "world!".

Definition test : unit :=
  eval_M prg (fun _ => tt).

Test test.