From Metaprog Require Import Prelude.
From Metaprog Require Export MetaTheory.Typing.

(** This module proves the subject reduction (aka preservation) lemma:
    reducing a well-typed term doesn't change its type. *)

(** Beta reduction preserves typing. *)
Lemma typing_beta {s} Σ Γ x ty body arg args (T : term s) :
  typing_evar_map Σ ->
  typing_context Σ Γ ->
  Σ ;; Γ ⊢ TApp (TLam x ty body) (arg :: args) : T ->
  Σ ;; Γ ⊢ TApp (body[x := arg]) args : T.
Proof.
intros HΣ HΓ H. pose proof (HT := typing_validity _ _ _ _ HΣ HΓ H).
apply typing_app_inv in H. destruct H as (f_ty & T' & H1 & H2 & H3).
apply typing_conv_type with T' ; [|assumption..]. clear T H3 HT.

apply typing_lam_inv in H1. destruct H1 as (body_ty & H1 & Hty & Hbody).
depelim H2. assert (x0 = x) as ->. { destruct x0 ; destruct x ; reflexivity. }
rewrite H0 in H1. apply conv_prod_inv in H1. clear f_ty H0. destruct H1 as (Ha & Hb).

assert (Hbody' : Σ ;; Γ ⊢ body[x := arg] : body_ty[x := arg]).
{
  apply typing_substitute with (CCons Γ x ty) ; [assumption|].
  apply typing_scons.
  - simpl_subst. apply typing_conv_type with a ; auto.
  - apply typing_sid.
}

assert (Hbody'' : Σ ;; Γ ⊢ body[x := arg] : b[x := arg]).
{
  apply typing_conv_type with (body_ty[x := arg]) ; [assumption | |].
  - now rewrite Hb.
  - change TType with (TType[x := arg]). eapply typing_substitute with (CCons Γ x a).
    + apply typing_prod_inv in H. apply H.
    + apply typing_scons ; [|apply typing_sid]. simpl_subst. assumption.
}
eapply typing_app ; eauto.
Qed.

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
