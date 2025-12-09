From Metaprog Require Import Prelude.

(** This module specifies how to extract basic data-types to OCaml.
    It makes heavy use of OCaml constants and functions defined
    in the plugin (file "plugin/extraction.ml"). *)

(*******************************************************************)
(** * OCaml functions used in Rocq. *)
(*******************************************************************)

(** Ocaml's [Obj.magic]. *)
Parameter ocaml_obj_magic : forall {A B}, A -> B.
Extract Inlined Constant ocaml_obj_magic => "Obj.magic".

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
(** * Extraction for persistent vectors. *)
(*******************************************************************)

(** This module defines persistent vectors [Vec.t A] on elements of type [A].
    Vectors are meant solely for extraction to OCaml: use with caution! *)
Module Vec.
  (** [Vec.t A] is the type of vectors with element type [A].
      Vectors can grow dynamically to accomodate more elements. *)
  Parameter t : Type -> Type.
  Extract Constant t "'a" => "'a MyPlugin.Extraction.Vec.t".

  (** Get the length of a vector. *)
  Parameter length : forall {A}, t A -> nat.
  Extract Inlined Constant length => "MyPlugin.Extraction.Vec.length".

  (** The empty vector. *)
  Parameter empty : forall {A}, unit -> t A.
  Extract Inlined Constant empty => "MyPlugin.Extraction.Vec.empty".

  (** Add an element to the end of a vector. *)
  Parameter add : forall {A}, t A -> A -> t A.
  Extract Inlined Constant add => "MyPlugin.Extraction.Vec.add".

  (** Remove the last element of a vector. Fails if the vector is empty. *)
  Parameter pop : forall {A}, t A -> t A * A.
  Extract Inlined Constant pop => "MyPlugin.Extraction.Vec.pop".

  (** Get an element at a specific index in a vector.
      Fails if the index is out of bounds. *)
  Parameter get : forall {A}, t A -> nat -> A.
  Extract Inlined Constant get => "MyPlugin.Extraction.Vec.get".

  (** Replace an element at a specific index in a vector.
      Fails if the index is out of bounds. *)
  Parameter set : forall {A}, t A -> nat -> A -> t A.
  Extract Inlined Constant set => "MyPlugin.Extraction.Vec.set".

End Vec.
