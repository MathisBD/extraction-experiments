From Metaprog Require Import Prelude Relations.
From Metaprog Require Export Data.Context MetaTheory.Reduction.SubstReduction.

(** This module defines:
    - One-step reduction of contexts [cred1].
    - Multi-step reduction of contexts [cred].
    And proves basic properties, notably an alternate induction principle
    [cred_ind_alt] which expresses the fact that [cred] is the reflexive
    transitive closure of [cred1].
*)

(***********************************************************************)
(** * One-step reduction of contexts. *)
(***********************************************************************)

(** [cred1 flags Σ Γ Γ'] means that context [Γ] reduces to context [Γ'] in
    exactly one reduction step. *)
Inductive cred1 (flags : red_flags) (Σ : evar_map) : forall {s}, context ∅ s -> context ∅ s -> Prop :=
| cred1_head {s} Γ x (ty ty' : term s) :
    Σ ⊢ ty ~>{flags} ty' ->
    cred1 flags Σ (CCons Γ x ty) (CCons Γ x ty')

| cred1_tail {s} Γ Γ' x (ty : term s) :
    cred1 flags Σ Γ Γ' ->
    cred1 flags Σ (CCons Γ x ty) (CCons Γ' x ty).

Derive Signature for cred1.

(***********************************************************************)
(** * Multi-step reduction of contexts. *)
(***********************************************************************)

(** [cred flags Σ Γ Γ'] means that context [Γ] reduces to context [Γ'] in
    zero or more reduction step.

    Note that we do not define [cred] as the reflexive-transitive closure
    of [cred1]: this fact is instead expressed by the lemma [cred_ind_alt]. *)
Inductive cred (flags : red_flags) (Σ : evar_map) : forall {s}, context ∅ s -> context ∅ s -> Prop :=
| cred_nil : cred flags Σ CNil CNil

| cred_cons {s} x (ty ty' : term s) Γ Γ' :
    Σ ⊢ ty ~~>{flags} ty' ->
    cred flags Σ Γ Γ' ->
    cred flags Σ (CCons Γ x ty) (CCons Γ' x ty').

Derive Signature for cred.

(***********************************************************************)
(** * Typeclass instances for setoid rewriting. *)
(***********************************************************************)

#[export] Instance cred_Reflexive flags Σ s : Reflexive (@cred flags Σ s).
Proof.
intros Γ. induction Γ ; constructor.
- reflexivity.
- assumption.
Qed.

#[export] Instance cred_Transitive flags Σ s : Transitive (@cred flags Σ s).
Proof.
intros Γ1 Γ2 Γ3 H1 H2. induction H1 ; depelim H2.
- reflexivity.
- constructor.
  + now rewrite H.
  + now apply IHcred.
Qed.

#[export] Instance cred_of_cred1 flags Σ s : subrelation (@cred1 flags Σ s) (@cred flags Σ s).
Proof.
intros Γ Γ' HΓ. induction HΓ ; constructor.
- now rewrite H.
- reflexivity.
- reflexivity.
- assumption.
Qed.

Lemma cred1_extend_flags {flags1 flags2 Σ s} :
  red_flags_incl flags1 flags2 ->
  subrelation (@cred1 flags1 Σ s) (@cred1 flags2 Σ s).
Proof.
intros Hf Γ Γ' HΓ. induction HΓ.
- constructor. eapply red1_extend_flags ; eassumption.
- constructor. assumption.
Qed.

Lemma cred_extend_flags {flags1 flags2 Σ s} :
  red_flags_incl flags1 flags2 ->
  subrelation (@cred flags1 Σ s) (@cred flags2 Σ s).
Proof.
intros Hf Γ Γ' HΓ. induction HΓ ; constructor.
- eapply red_extend_flags ; eassumption.
- assumption.
Qed.

Lemma cred1_extend_evm {flags Σ1 Σ2 s} :
  Σ1 ⊑ Σ2 ->
  subrelation (@cred1 flags Σ1 s) (@cred1 flags Σ2 s).
Proof.
intros HΣ Γ Γ' HΓ. induction HΓ.
- constructor. now apply (red1_extend_evm HΣ).
- constructor. assumption.
Qed.

Lemma cred_extend_evm {flags Σ1 Σ2 s} :
  Σ1 ⊑ Σ2 ->
  subrelation (@cred flags Σ1 s) (@cred flags Σ2 s).
Proof.
intros HΣ Γ Γ' HΓ. induction HΓ ; constructor.
- now apply (red_extend_evm HΣ).
- assumption.
Qed.

(***********************************************************************)
(** * Lemmas about context reduction. *)
(***********************************************************************)

Section Lemmas.
  Context {flags : red_flags} {Σ : evar_map}.

  Lemma lookup_context_cred1 {s} (i : index s) Γ Γ' :
    cred1 flags Σ Γ Γ' ->
    Σ ⊢ lookup_context i Γ ~>{flags} lookup_context i Γ' \/
    lookup_context i Γ = lookup_context i Γ'.
  Proof.
  intros Hred. induction Hred ; depelim i ; simp lookup_context ; simpl_subst.
  - left. now apply red1_rename.
  - now right.
  - now right.
  - destruct (IHHred i) as [H1 | H2].
    + left. apply red1_rename. apply H1.
    + right. now rewrite H2.
  Qed.

  Lemma lookup_context_cred {s} (i : index s) Γ Γ' :
    cred flags Σ Γ Γ' ->
    Σ ⊢ lookup_context i Γ ~~>{flags} lookup_context i Γ'.
  Proof.
  intros H. induction H ; depelim i ; simp lookup_context ; simpl_subst.
  - now rewrite H.
  - now rewrite IHcred.
  Qed.

  Lemma cred_is_clos_cred1_aux1 {s x} (Γ Γ' : context ∅ s) ty :
    refl_trans_clos (cred1 flags Σ) Γ Γ' ->
    refl_trans_clos (cred1 flags Σ) (CCons Γ x ty) (CCons Γ' x ty).
  Proof.
  intros H. induction H.
  - reflexivity.
  - rewrite IHrefl_trans_clos. apply refl_trans_clos_one. now constructor.
  Qed.

  Lemma cred_is_clos_cred1_aux2 {s x} (Γ : context ∅ s) ty ty' :
    Σ ⊢ ty ~>{flags} ty' ->
    refl_trans_clos (cred1 flags Σ) (CCons Γ x ty) (CCons Γ x ty').
  Proof. intros H. apply refl_trans_clos_one. now constructor. Qed.

  (** [cred] is the reflexive-transitive closure of [cred1].
      The lemma [cred_ind_alt] is usually more useful. *)
  Lemma cred_is_clos_cred1 {s} (Γ Γ' : context ∅ s) :
    cred flags Σ Γ Γ' <-> refl_trans_clos (cred1 flags Σ) Γ Γ'.
  Proof.
  split ; intros H.
  - induction H.
    + reflexivity.
    + induction H.
      * now apply cred_is_clos_cred1_aux1.
      * rewrite IHred. now apply cred_is_clos_cred1_aux2.
  - induction H.
    + reflexivity.
    + rewrite IHrefl_trans_clos, H0. reflexivity.
  Qed.

End Lemmas.

(** Alternate induction principle for [cred] which expresses the fact that
    [cred] is the reflexive-transitive closure of [cred1]. *)
Lemma cred_ind_alt flags Σ (P : forall s, context ∅ s -> context ∅ s -> Prop)
  (Hrefl : forall s Γ, P s Γ Γ)
  (Hstep : forall s Γ1 Γ2 Γ3,
    cred flags Σ Γ1 Γ2 -> P s Γ1 Γ2 ->
    cred1 flags Σ Γ2 Γ3 ->
    P s Γ1 Γ3) :
  forall s Γ1 Γ2, cred flags Σ Γ1 Γ2 -> P s Γ1 Γ2.
Proof.
intros s Γ1 Γ2 H. rewrite cred_is_clos_cred1 in H. induction H.
- apply Hrefl.
- apply Hstep with y ; auto. now rewrite cred_is_clos_cred1.
Qed.
