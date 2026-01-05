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

(** [cred1 Σ Γ Γ'] means that context [Γ] reduces to context [Γ'] in
    exactly one reduction step. *)
Inductive cred1 (Σ : evar_map) : forall {s}, context ∅ s -> context ∅ s -> Prop :=
| cred1_head {s} Γ x (ty ty' : term s) :
    Σ ⊢ ty ~> ty' ->
    cred1 Σ (CCons Γ x ty) (CCons Γ x ty')

| cred1_tail {s} Γ Γ' x (ty : term s) :
    cred1 Σ Γ Γ' ->
    cred1 Σ (CCons Γ x ty) (CCons Γ' x ty).

Derive Signature for cred1.

Lemma lookup_context_cred1 {s Σ} (i : index s) Γ Γ' :
  cred1 Σ Γ Γ' ->
  Σ ⊢ lookup_context i Γ ~> lookup_context i Γ' \/
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

(***********************************************************************)
(** * Multi-step reduction of contexts. *)
(***********************************************************************)

(** [cred Σ Γ Γ'] means that context [Γ] reduces to context [Γ'] in
    zero or more reduction step. *)
Inductive cred (Σ : evar_map) : forall {s}, context ∅ s -> context ∅ s -> Prop :=
| cred_nil : cred Σ CNil CNil

| cred_cons {s} x (ty ty' : term s) Γ Γ' :
    Σ ⊢ ty ~~> ty' ->
    cred Σ Γ Γ' ->
    cred Σ (CCons Γ x ty) (CCons Γ' x ty').

Derive Signature for cred.

#[export] Instance cred_Reflexive Σ s : Reflexive (@cred Σ s).
Proof.
intros Γ. induction Γ ; constructor.
- reflexivity.
- assumption.
Qed.

#[export] Instance cred_Transitive Σ s : Transitive (@cred Σ s).
Proof.
intros Γ1 Γ2 Γ3 H1 H2. induction H1 ; depelim H2.
- reflexivity.
- constructor.
  + now rewrite H.
  + now apply IHcred.
Qed.

#[export] Instance cred_of_cred1 Σ s : subrelation (@cred1 Σ s) (@cred Σ s).
Proof.
intros Γ Γ' HΓ. induction HΓ ; constructor.
- now rewrite H.
- reflexivity.
- reflexivity.
- assumption.
Qed.

Lemma cred_is_clos_cred1_aux1 {s x} Σ (Γ Γ' : context ∅ s) ty :
  refl_trans_clos (cred1 Σ) Γ Γ' ->
  refl_trans_clos (cred1 Σ) (CCons Γ x ty) (CCons Γ' x ty).
Proof.
intros H. induction H.
- reflexivity.
- rewrite IHrefl_trans_clos. apply refl_trans_clos_one. now constructor.
Qed.

Lemma cred_is_clos_cred1_aux2 {s x} Σ (Γ : context ∅ s) ty ty' :
  Σ ⊢ ty ~> ty' ->
  refl_trans_clos (cred1 Σ) (CCons Γ x ty) (CCons Γ x ty').
Proof. intros H. apply refl_trans_clos_one. now constructor. Qed.

Lemma cred_is_clos_cred1 {s} Σ (Γ Γ' : context ∅ s) :
  cred Σ Γ Γ' <-> refl_trans_clos (cred1 Σ) Γ Γ'.
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

(** Alternate induction principle for [cred] which expresses the fact that
    [cred] is the reflexive-transitive closure of [cred1]. *)
Lemma cred_ind_alt (Σ : evar_map) (P : forall s, context ∅ s -> context ∅ s -> Prop)
  (Hrefl : forall s Γ, P s Γ Γ)
  (Hstep : forall s Γ1 Γ2 Γ3,
    cred Σ Γ1 Γ2 -> P s Γ1 Γ2 ->
    cred1 Σ Γ2 Γ3 ->
    P s Γ1 Γ3) :
  forall s Γ1 Γ2, cred Σ Γ1 Γ2 -> P s Γ1 Γ2.
Proof.
intros s Γ1 Γ2 H. rewrite cred_is_clos_cred1 in H. induction H.
- apply Hrefl.
- apply Hstep with y ; auto. now rewrite cred_is_clos_cred1.
Qed.

Lemma lookup_context_cred {s Σ} (i : index s) Γ Γ' :
  cred Σ Γ Γ' ->
  Σ ⊢ lookup_context i Γ ~~> lookup_context i Γ'.
Proof.
intros H. induction H ; depelim i ; simp lookup_context ; simpl_subst.
- now rewrite H.
- now rewrite IHcred.
Qed.
