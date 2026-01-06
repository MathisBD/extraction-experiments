From Metaprog Require Import Prelude.
From Metaprog Require Export Data.Evars Control.Meta.

(** The effect [evarE] provides access to the evar-map, which stores information
    about evars. *)
Variant evarE : Type -> Type :=
| FreshEvar : term ∅ -> evarE evar_id
| LookupEvar : evar_id -> evarE (option evar_entry)
| DefineEvar : evar_id -> term ∅ -> evarE unit.

Section EvarOperations.
  Context {E} `{evarE -< E}.

  (** Create a fresh evar with the given type. Rets the id of the new evar. *)
  Definition fresh_evar (ty : term ∅) : meta E evar_id :=
    trigger (FreshEvar ty).

  (** Lookup the entry associated to an evar. Rets [None] if the evar doesn't exist. *)
  Definition lookup_evar (ev : evar_id) : meta E (option evar_entry) :=
    trigger (LookupEvar ev).

  (** Get the type of an evar. Rets [None] if the evar doesn't exist. *)
  Definition lookup_evar_type (ev : evar_id) : meta E (option (term ∅)) :=
    let% entry_opt := lookup_evar ev in
    match entry_opt with
    | Some {| evar_type := ty ; evar_def := _ |} => ret $ Some ty
    | None => ret None
    end.

  (** Get the definition of an evar. Rets [None] if the evar doesn't exist
      of doesn't have a definition. *)
  Definition lookup_evar_def (ev : evar_id) : meta E (option (term ∅)) :=
    let% entry_opt := lookup_evar ev in
    match entry_opt with
    | Some {| evar_type := _ ; evar_def := Some def |} => ret $ Some def
    | _ => ret None
    end.

  (** Set the definition of an evar. Fails if the evar is already defined,
      or if the definition doesn't have the correct type. *)
  Definition define_evar (ev : evar_id) (def : term ∅) : meta E unit :=
    trigger (DefineEvar ev def).

End EvarOperations.