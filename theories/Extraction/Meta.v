From Metaprog Require Import Prelude Control.Meta Extraction.Data.

(** This module specifies how to extract the meta-programming monad
    and effects to OCaml. *)

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
Record fun_entry (E : Type -> Type) := mk_entry {
  entry_dom : Type ;
  entry_codom : entry_dom -> Type ;
  entry_fun : forall a : entry_dom, meta E (entry_codom a)
}.

Arguments entry_dom {E}.
Arguments entry_codom {E}.
Arguments entry_fun {E}.