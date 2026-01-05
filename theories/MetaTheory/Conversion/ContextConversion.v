From Metaprog Require Import Prelude.
From Metaprog.MetaTheory Require Export Conversion.SubstConversion.

(** This module defines the conversion relation [cconv] on contexts
    and proves basic lemmas, notably the Church-Rosser lemma for contexts. *)

(***********************************************************************)
(** * Conversion relation on contexts. *)
(***********************************************************************)

(** [cconv flags Σ Γ Γ'] means that contexts [Γ] and [Γ'] are convertible
    in evar-map [Σ]. *)
Inductive cconv (flags : red_flags) (Σ : evar_map) : forall {s}, context ∅ s -> context ∅ s -> Prop :=
| cconv_nil : cconv flags Σ CNil CNil

| cconv_cons {s} x (ty ty' : term s) Γ Γ' :
    Σ ⊢ ty ≡{flags} ty' ->
    cconv flags Σ Γ Γ' ->
    cconv flags Σ (CCons Γ x ty) (CCons Γ' x ty').

Derive Signature for cconv.

(***********************************************************************)
(** * Typeclass instances for setoid rewriting. *)
(***********************************************************************)

Section Instances.
  Context {flags : red_flags} {Σ : evar_map}.

  #[export] Instance cconv_Reflexive s : Reflexive (@cconv flags Σ s).
  Proof.
  intros Γ. induction Γ ; constructor.
  - reflexivity.
  - assumption.
  Qed.

  #[export] Instance cconv_Symmetric s : Symmetric (@cconv flags Σ s).
  Proof.
  intros Γ Γ' HΓ. induction HΓ ; constructor.
  - now symmetry.
  - assumption.
  Qed.

  #[export] Instance cconv_Transitive s : Transitive (@cconv flags Σ s).
  Proof.
  intros Γ1 Γ2 Γ3 H1 H2. induction H1 ; depelim H2.
  - reflexivity.
  - constructor.
    + now rewrite H.
    + now apply IHcconv.
  Qed.

  #[export] Instance cconv_of_cred1 s : subrelation (@cred1 flags Σ s) (@cconv flags Σ s).
  Proof.
  intros Γ Γ' HΓ. induction HΓ ; constructor.
  - now rewrite H.
  - reflexivity.
  - reflexivity.
  - assumption.
  Qed.

  #[export] Instance cconv_of_cred s : subrelation (@cred flags Σ s) (@cconv flags Σ s).
  Proof.
  intros Γ Γ' HΓ. induction HΓ ; constructor.
  - now rewrite H.
  - assumption.
  Qed.

End Instances.

Lemma cconv_extend_flags {flags1 flags2 Σ s} :
  red_flags_incl flags1 flags2 ->
  subrelation (@cconv flags1 Σ s) (@cconv flags2 Σ s).
Proof.
intros Hf Γ Γ' HΓ. induction HΓ ; constructor.
- now apply (conv_extend_flags Hf).
- assumption.
Qed.

(***********************************************************************)
(** * Lemmas about context conversion. *)
(***********************************************************************)

Section Lemmas.
  Context {flags : red_flags} {Σ : evar_map}.

  Lemma lookup_context_cconv {s} (i : index s) Γ Γ' :
    cconv flags Σ Γ Γ' ->
    Σ ⊢ lookup_context i Γ ≡{flags} lookup_context i Γ'.
  Proof.
  intros H. induction H ; depelim i ; simp lookup_context ; simpl_subst.
  - now rewrite H.
  - now rewrite IHcconv.
  Qed.

End Lemmas.
