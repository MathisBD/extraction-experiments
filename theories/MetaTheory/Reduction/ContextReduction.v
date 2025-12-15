From Metaprog Require Import Prelude.
From Metaprog Require Export Data.Context MetaTheory.Reduction.SubstReduction.

(** This module defines:
    - One-step reduction of contexts [cred1].
    - Multi-step reduction of contexts [cred].
    And proves basic properties.
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
- unfold eq_rect in H. cbn in H. depelim H. reflexivity.
- unfold eq_rect in H3. cbn in H3. depelim H3. constructor.
  + rewrite H. admit.
  + apply IHcred. admit.
(* Equations issue: I need NoConfusionHom on [context]. *)
Admitted.

#[export] Instance cred_of_cred1 Σ s : subrelation (@cred1 Σ s) (@cred Σ s).
Proof.
intros Γ Γ' HΓ. induction HΓ ; constructor.
- now rewrite H.
- reflexivity.
- reflexivity.
- assumption.
Qed.

Lemma lookup_context_cred {s Σ} (i : index s) Γ Γ' :
  cred Σ Γ Γ' ->
  Σ ⊢ lookup_context i Γ ~~> lookup_context i Γ'.
Proof.
intros H. induction H ; depelim i ; simp lookup_context ; simpl_subst.
- now rewrite H.
- now rewrite IHcred.
Qed.
