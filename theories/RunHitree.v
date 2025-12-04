From Metaprog Require Export Prelude Hitree Loader.

(** This file specifies how to extract and run interaction trees.
    It makes heavy use of OCaml constants and functions defined
    in the plugin (file "plugin/extraction.ml"). *)

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
Extract Inductive prod => "(*)" [ "(,)" ].

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

(** Extraction for primitive strings. *)
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
(** * Extraction for mutable vectors. *)
(*******************************************************************)

(** This module defines persistent vectors [Vec.t A] on elements of type [A].
    Vectors are meant solely for extraction to OCaml: use with caution! *)
Module Vec.
  Parameter t : Type -> Type.
  Extract Constant t "'a" => "'a MyPlugin.Extraction.Vec.t".

  Parameter empty : forall {A}, unit -> t A.
  Extract Inlined Constant empty => "MyPlugin.Extraction.Vec.empty".

  Parameter add : forall {A}, t A -> A -> t A.
  Extract Inlined Constant add => "MyPlugin.Extraction.Vec.add".

  Parameter pop : forall {A}, t A -> t A * A.
  Extract Inlined Constant pop => "MyPlugin.Extraction.Vec.pop".

  Parameter get : forall {A}, t A -> nat -> A.
  Extract Inlined Constant get => "MyPlugin.Extraction.Vec.get".

  Parameter set : forall {A}, t A -> nat -> A -> t A.
  Extract Inlined Constant set => "MyPlugin.Extraction.Vec.set".

  Parameter length : forall {A}, t A -> nat.
  Extract Inlined Constant length => "MyPlugin.Extraction.Vec.length".

End Vec.

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
