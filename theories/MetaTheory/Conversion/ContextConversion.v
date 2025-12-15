From Metaprog Require Import Prelude.
From Metaprog.MetaTheory Require Export Conversion.SubstConversion.

(** This module defines the conversion relation [cconv] on contexts
    and proves basic lemmas, notably the Church-Rosser lemma for contexts. *)

(***********************************************************************)
(** * Conversion relation on contexts. *)
(***********************************************************************)

(** [cconv Σ Γ Γ'] means that contexts [Γ] and [Γ'] are convertible
    in evar-map [Σ]. *)
Inductive cconv (Σ : evar_map) : forall {s}, context ∅ s -> context ∅ s -> Prop :=
| cconv_nil : cconv Σ CNil CNil

| cconv_cons {s} x (ty ty' : term s) Γ Γ' :
    Σ ⊢ ty ≡ ty' ->
    cconv Σ Γ Γ' ->
    cconv Σ (CCons Γ x ty) (CCons Γ' x ty').

Derive Signature for cconv.

#[export] Instance cconv_Reflexive Σ s : Reflexive (@cconv Σ s).
Proof.
intros Γ. induction Γ ; constructor.
- reflexivity.
- assumption.
Qed.

#[export] Instance cconv_Symmetric Σ s : Symmetric (@cconv Σ s).
Proof.
intros Γ Γ' HΓ. induction HΓ ; constructor.
- now symmetry.
- assumption.
Qed.

#[export] Instance cconv_Transitive Σ s : Transitive (@cconv Σ s).
Proof.
intros Γ1 Γ2 Γ3 H1 H2. induction H1 ; depelim H2.
- unfold eq_rect in H. cbn in H. depelim H. reflexivity.
- unfold eq_rect in H3. cbn in H3. depelim H3. constructor.
  + rewrite H. admit.
  + apply IHcconv. admit.
(* Equations issue: I need NoConfusionHom on [context]. *)
Admitted.

#[export] Instance cconv_of_cred1 Σ s : subrelation (@cred1 Σ s) (@cconv Σ s).
Proof.
intros Γ Γ' HΓ. induction HΓ ; constructor.
- now rewrite H.
- reflexivity.
- reflexivity.
- assumption.
Qed.

#[export] Instance cconv_of_cred Σ s : subrelation (@cred Σ s) (@cconv Σ s).
Proof.
intros Γ Γ' HΓ. induction HΓ ; constructor.
- now rewrite H.
- assumption.
Qed.

Lemma lookup_context_cconv {s Σ} (i : index s) Γ Γ' :
  cconv Σ Γ Γ' ->
  Σ ⊢ lookup_context i Γ ≡ lookup_context i Γ'.
Proof.
intros H. induction H ; depelim i ; simp lookup_context ; simpl_subst.
- now rewrite H.
- now rewrite IHcconv.
Qed.
