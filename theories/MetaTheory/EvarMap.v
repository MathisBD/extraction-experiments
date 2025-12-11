From Metaprog Require Import Prelude.
From Metaprog Require Export Data.Evars.

(** This module defines the logical view of evar maps. This representation is inefficient,
    but we do not extract it to OCaml: meta-programs instead use Rocq's built-in evar map.

    An advantage of the definition of evar maps as done here is _extensionality_:
    to prove that two evars maps are equal, it suffices to prove pointwise equality
    (and same thing for )*)

(** The logical view of the evar map used in proofs.

    We say that an evar is:
    - "absent" if its entry is [None].
    - "present" if its entry is [Some _].
    - "undefined" if it is present and has no definition.
    - "defined" if it is present and has a definition.*)
Definition evar_map := evar_id -> option evar_entry.

(** Inclusion on (optional) evar entries. *)
Inductive entry_incl : option evar_entry -> option evar_entry -> Prop :=
(** If the first evar is absent from the evar map,
    the second evar can have any entry associated to it. *)
| entry_incl_absent entry_opt :
    entry_incl None entry_opt
(** If the first evar is undefined, the second evar must be present and have the same type. *)
| entry_incl_undef ty def_opt :
    entry_incl (Some (mk_evar_entry ty None)) (Some (mk_evar_entry ty def_opt))
(** If the first evar is defined, the second evar must be defined and have the same type
    and definition. *)
| entry_incl_def ty def :
    entry_incl (Some (mk_evar_entry ty (Some def))) (Some (mk_evar_entry ty (Some def))).

Derive Signature for entry_incl.

(** Inclusion on evar maps, also written [Σ ⊑ Σ']. *)
Definition evar_map_incl (Σ Σ' : evar_map) : Prop :=
  forall ev, entry_incl (Σ ev) (Σ' ev).

Notation "Σ1 ⊑ Σ2" := (evar_map_incl Σ1 Σ2)
  (at level 30, no associativity).

(** Extensionality lemma for evar maps. *)
Lemma evm_ext (Σ Σ' : evar_map) :
  (forall ev, Σ ev = Σ' ev) ->
  Σ = Σ'.
Proof. intros H. fun_ext ev. apply H. Qed.

(** [evm_ext] is the analog of [fun_ext] but for evar-maps. *)
Tactic Notation "evm_ext" ident(x) :=
  apply evm_ext ; intro x.