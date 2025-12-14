From Metaprog Require Import Prelude.
From Metaprog Require Export MetaTheory.Typing.

(** This module proves the subject reduction (aka preservation) lemma:
    reducing a well-typed term doesn't change its type. *)

(***********************************************************************)
(** * Context conversion. *)
(***********************************************************************)

Inductive conv_context (Σ : evar_map) : forall {s}, context ∅ s -> context ∅ s -> Prop :=
| conv_context_nil : conv_context Σ CNil CNil
| conv_context_cons {s} Γ Γ' x (ty ty' : term s) :
    conv_context Σ Γ Γ' ->
    Σ ⊢ ty ≡ ty' ->
    conv_context Σ (CCons Γ x ty) (CCons Γ' x ty').

Derive Signature for conv_context.

#[export] Instance conv_context_Reflexive s Σ : Reflexive (@conv_context Σ s).
Proof. intros Γ. induction Γ ; now constructor. Qed.

#[export] Instance conv_context_Symmetric s Σ : Symmetric (@conv_context Σ s).
Proof. intros Γ Γ' H. induction H ; now constructor. Qed.

Lemma conv_context_lookup {s} Σ Γ Γ' (i : index s) :
  conv_context Σ Γ Γ' ->
  Σ ⊢ lookup_context i Γ ≡ lookup_context i Γ'.
Proof.
intros H. induction H.
- reflexivity.
- depelim i ; simp lookup_context.
  + unfold wk. now apply conv_rename.
  + unfold wk. now apply conv_rename.
Qed.

(*Lemma aux {s} Σ Γ Γ' (i : index s) :
  conv_context Σ Γ Γ' ->
  typing_context Σ Γ' ->
  Σ ;; Γ' ⊢ lookup_context i Γ : TType.
Proof.
intros H. induction H ; intros H' ; depelim i ; simp lookup_context ; simpl_subst.
- change TType with (rename (@rshift s x) TType). apply typing_rename with Γ'.
  + depelim H'. admit.
  + apply typing_rshift.*)

(*Lemma typing_conv_context {s} Σ Γ Γ' (t T : term s) :
  Σ ;; Γ ⊢ t : T ->
  conv_context Σ Γ Γ' ->
  typing_context Σ Γ' ->
  Σ ;; Γ' ⊢ t : T.
Proof.
intros Ht. induction Ht ; intros HΓ1 HΓ2.
- constructor.
- subst. apply typing_conv_type with (lookup_context i Γ').
  + now apply typing_var.
  + symmetry. now apply conv_context_lookup.
  + apply H
Admitted.*)

(** Beta reduction preserves typing. *)
Lemma typing_beta {s} Σ Γ x ty body arg args (T : term s) :
  typing_evar_map Σ ->
  typing_context Σ Γ ->
  Σ ;; Γ ⊢ TApp (TLam x ty body) (arg :: args) : T ->
  Σ ;; Γ ⊢ TApp (body[x := arg]) args : T.
Proof.
intros HΣ HΓ H. pose proof (HT := typing_type_ok _ _ _ _ HΣ HΓ H).
apply typing_app_inv in H. destruct H as (f_ty & T' & H1 & H2 & H3).
apply typing_conv_type with T' ; [|assumption..]. clear T H3 HT.

apply typing_lam_inv in H1. destruct H1 as (body_ty & H1 & Hty & Hbody).
depelim H2. assert (x0 = x) as ->. { destruct x0 ; destruct x ; reflexivity. }
apply conv_prod_inv in H1. destruct H1 as (Ha & Hb).
apply typing_app with (b[x := arg]). ; [|assumption].


rewrite H1 in H0. clear f_ty H1. apply conv_prod_inv in H0. destruct H0 as (Ha & Hb).
eapply typing_app with (b[x := arg]) ; [|assumption].
apply typing_substitute with (CCons Γ x a).
(*- apply typing_conv_type with body_ty ; auto.
  apply typing_prod_inv in H. apply typing_conv_context with (CCons Γ x a).
  + apply H.
  + admit.
  + constructor.
- apply typing_scons ; simpl_subst.
  + apply typing_conv_type with a ; auto. now symmetry.
  + apply typing_sid.
Qed.*)
Admitted.

(** One-step reduction preserves typing. *)
Lemma typing_red1 {s} Σ Γ (t u T : term s) :
  typing_evar_map Σ ->
  typing_context Σ Γ ->
  Σ ;; Γ ⊢ t : T ->
  Σ ⊢ t ~>₁ u ->
  Σ ;; Γ ⊢ u : T.
Proof.
intros HΣ HΓ Ht Hred. depind Hred.
- eapply typing_beta ; eauto.
- eapply typing_evar_expand ; eauto.
- admit.
- apply typing_lam_inv in Ht. destruct Ht as (body_ty & HT & Hty & Hbody).
  apply IHHred in Hbody ; auto.
  + apply typing_conv_type with (TProd x ty body_ty).
    * apply typing_lam ; auto.
    * now symmetry.
    *
  + constructor ; auto.

(*apply typing_lam_inv in Ht. destruct Ht as (body_ty & H1 & Hty & Hbody).
  apply IHHred in Hty ; auto. rewrite Hred in H1.
  apply typing_conv_type with (TProd x ty' body_ty).
  + apply typing_lam.
    * assumption.
    *

  apply typing_lam. apply IHHred.*)


apply HΣ in H. depelim H.  depelim Ht. apply typing_evar_entry.

Admitted.

(** Evar expansion preserves typing. *)
Lemma typing_evar_expand {s} Σ Γ ev ty def (T : term s) :
  typing_evar_map Σ ->
  typing_context Σ Γ ->
  Σ ;; Γ ⊢ TEvar ev : T ->
  Σ ev = Some (mk_evar_entry ty (Some def)) ->
  Σ ;; Γ ⊢ wk def : T.
Proof.
intros HΣ HΓ Hev Hentry. apply typing_conv_type with (wk ty).
- unfold wk. apply typing_rename with CNil.
  + apply HΣ in Hentry. depelim Hentry. assumption.
  + intros i. depelim i.
- apply typing_evar_inv in Hev. destruct Hev as (entry & H & HT).
  rewrite H in Hentry. depelim Hentry. cbn in HT. now symmetry.
- eapply typing_type_ok ; eauto.
Qed.


(** Changing a term to a convertible one doesn't change its type. *)
Lemma typing_conv {s} Σ Γ (t u T : term s) :
  Σ ;; Γ ⊢ t : T ->
  Σ ⊢ t ≡ u ->
  Σ ;; Γ ⊢ u : T.
Proof. Admitted.

#[export] Instance typing_conv_Proper {s} Σ Γ :
  Proper (conv Σ ==> eq ==> iff) (@typing s Σ Γ).
Proof.
intros t t' Ht T T' ->. split ; intros H ; eapply typing_conv ; eauto. now symmetry.
Qed.
