From Metaprog Require Import Prelude.
From Metaprog Require Export MetaTheory.Typing.TermTyping.

(** This module defines a notion of typing for evar-maps. *)

(***********************************************************************)
(** * Typing evar-maps. *)
(***********************************************************************)

(** [typing_evar_entry Σ e] asserts that the evar-entry [e] is well-typed
    in evar-map [Σ]. *)
Inductive typing_evar_entry (Σ : evar_map) : evar_entry -> Prop :=

(** An undefined evar entry is well-typed if the type if well-typed. *)
| typing_evar_undefined ty :
    Σ ;; CNil ⊢ ty : TType ->
    typing_evar_entry Σ (mk_evar_entry ty None)

(** A defined evar entry is well-typed if the type is well-typed
    and the definition has the correct type. *)
| typing_evar_defined ty def :
    Σ ;; CNil ⊢ ty : TType ->
    Σ ;; CNil ⊢ def : ty ->
    typing_evar_entry Σ (mk_evar_entry ty (Some def)).

Derive Signature for typing_evar_entry.

(** [typing_evar_map Σ] means that the evar-map [Σ] is well-typed.
    We do _not_ check that the evar-map is acyclic:
    this would likely be very annoying to do. *)
Definition typing_evar_map (Σ : evar_map) :=
  forall ev entry, Σ ev = Some entry -> typing_evar_entry Σ entry.

(***********************************************************************)
(** * Properties of evar-map typing. *)
(***********************************************************************)

Lemma typing_evar_type Σ entry :
  typing_evar_entry Σ entry ->
  Σ ;; CNil ⊢ entry.(evar_type) : TType.
Proof. intros H. destruct H ; cbn ; assumption. Qed.
