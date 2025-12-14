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
- eapply typing_validity ; eauto.
Qed.

Reserved Notation "Σ ⊢ Γ1 '~>ctx' Γ2"
  (at level 50, Γ1 at next level, Γ2 at next level).

(** Context reduction. *)
Inductive red1_context (Σ : evar_map) : forall {s}, context ∅ s -> context ∅ s -> Prop :=
| red1_context_head {s} Γ x (ty ty' : term s) :
    Σ ⊢ ty ~> ty' ->
    Σ ⊢ CCons Γ x ty ~>ctx CCons Γ x ty'

| red1_context_tail {s} Γ Γ' x (ty : term s) :
    Σ ⊢ Γ ~>ctx Γ' ->
    Σ ⊢ CCons Γ x ty ~>ctx CCons Γ' x ty

where "Σ ⊢ Γ1 '~>ctx' Γ2" := (red1_context Σ Γ1 Γ2).

Derive Signature for red1_context.

(*Lemma typing_red1_var {s} Σ Γ (i : index s) :
  typing_evar_map Σ ->
  typing_context Σ Γ ->
  forall Γ',
    Σ ⊢ Γ ~>ctx Γ' ->
    Σ ;; Γ' ⊢ TVar i : lookup_context i Γ.
Proof.
intros HΣ HΓ. induction HΓ ; intros Γ' Hred.
- depelim Hred.
- depelim Hred ; depelim i ; simp lookup_context ; simpl_subst.
  + cbn in H1. depelim H1.
    assert (Γ0 = Γ) as -> by admit.
    assert (ty0 = ty) as -> by admit.
    clear H1 H3 H3'.*)

(** One-step reduction preserves typing. *)
Lemma typing_red1_aux {s} Σ Γ (t T : term s) :
  typing_evar_map Σ ->
  typing_context Σ Γ ->
  Σ ;; Γ ⊢ t : T ->
  (forall t', Σ ⊢ t ~> t' -> Σ ;; Γ ⊢ t' : T) /\
  (forall Γ', Σ ⊢ Γ ~>ctx Γ' -> Σ ;; Γ' ⊢ t : T).
Proof.
intros HΣ HΓ Ht. induction Ht ; (split ; [intros t' Hred | intros Γ' Hred]).
- depelim Hred.
- constructor.
- depelim Hred.
- subst. apply typing_conv_type with (lookup_context i Γ').
  + now constructor.
  + admit.
  +
admit.
  (*
  H1 : Σ ;; Γ ⊢ ty : TType
  H2 : Σ ;; CCons Γ x ty ⊢ TVar I0 : wk ty
  Hred : CCons Γ x ty ~> Γ'
  IH: forall ty', Σ ⊢ ty ~> ty' -> Σ ;; Γ ⊢ ty' : TType

  Case 1:
    CCons Γ x ty ~> CCons Γ x ty' because Σ ⊢ ty ~> ty'
    We need to show:
      Σ ;; CCons Γ x ty' ⊢ TVar I0 : wk ty




  *)

- constructor.
  + now apply IHHt1.
  + apply IHHt2 ; auto ; now constructor.
- depelim Hred.
  + apply typing_conv_type with (TProd x ty' body_ty).
    * constructor.
      --now apply IHHt1.
      --apply IHHt2 ; auto ; now constructor.
    * now rewrite Hred.
    * constructor ; auto. eapply typing_validity ; eauto.
      constructor ; auto.
  + constructor ; auto. apply IHHt2 ; auto. now constructor.
- constructor.
  + now apply IHHt1.
  + apply IHHt2 ; auto ; now constructor.
- depelim Hred.
  + constructor.
    * apply IHHt1 ; auto.
    * apply IHHt2 ; auto ; now constructor.
  + constructor ; auto. apply IHHt2 ; auto. now constructor.
- apply typing_app with f_ty ; [now apply IHHt |].
  clear f Ht IHHt. induction H ; econstructor ; try eassumption.
  + apply H ; auto.
  + apply H1 ; auto.
- depelim Hred.
  + eapply typing_beta ; eauto. apply typing_app with f_ty ; eauto.
    revert H. apply All_spine_consequence. firstorder.
  + apply typing_app with f_ty ; [now apply IHHt |].
    revert H. apply All_spine_consequence. firstorder.
  + apply typing_app with f_ty ; [assumption |].
    clear f IHHt Ht. revert f_ty T H. induction H0.
    * intros f_ty T H1. depelim H1. eapply All_spine_cons ; eauto.
      --now destruct H0.
      --apply H2 ; auto.
      --
    * intros f_ty T H. depelim H. econstructor ; eauto.
      --now destruct H.
      --now destruct H2.
- now constructor.
- depelim Hred. rewrite H in H0. depelim H0. cbn. unfold wk. eapply typing_rename.
  + apply HΣ in H. depelim H. eassumption.
  + intros i. depelim i.
- apply typing_conv_type with A ; auto.
  + now apply IHHt1.
  + now apply IHHt2.
- apply typing_conv_type with A ; auto. now apply IHHt1.
Admitted.



Definition conv_context {s} Σ (Γ Γ' : context ∅ s) :=
  forall i,
    Σ ⊢ lookup_context i Γ ≡ lookup_context i Γ' /\
    Σ ;; Γ' ⊢ lookup_context i Γ : TType.

Lemma typing_conv_context {s} Σ (Γ : context ∅ s) t T :
  Σ ;; Γ ⊢ t : T ->
  forall Γ',
  conv_context Σ Γ Γ' ->
  Σ ;; Γ' ⊢ t : T.
Proof.
intros H. induction H ; intros Γ' HΓ.
- constructor.
- subst. apply typing_conv_type with (lookup_context i Γ').
  + now constructor.
  + symmetry. apply HΓ.
  + apply HΓ. Check typing_conv_type.
- constructor ; auto. apply IHtyping2. intros i ; depelim i ; simp lookup_context ; simpl_subst.
  + split ; [reflexivity |]. change TType with (rename (@rshift s x) TType).
    eapply typing_rename ; eauto. apply typing_rshift.


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
- pose proof (Ht' := Ht). apply typing_lam_inv in Ht'. destruct Ht' as (body_ty & HT & Hty & Hbody).
  specialize (IHHred Γ TType HΣ HΓ Hty).
  apply typing_conv_type with (TProd x ty' body_ty).
  + constructor ; auto. admit.
  + rewrite <-Hred. now symmetry.
  + eapply typing_validity ; eauto.


- pose proof (Ht' := Ht). apply typing_lam_inv in Ht'. destruct Ht' as (body_ty & HT & Hty & Hbody).
  specialize (IHHred (CCons Γ x ty) body_ty HΣ). feed IHHred. { constructor ; auto. }
  feed IHHred. { assumption. }
  apply typing_conv_type with (TProd x ty body_ty).
  + constructor ; auto.
  + now symmetry.
  + eapply typing_validity ; eauto.
- admit.


(*apply typing_lam_inv in Ht. destruct Ht as (body_ty & H1 & Hty & Hbody).
  apply IHHred in Hty ; auto. rewrite Hred in H1.
  apply typing_conv_type with (TProd x ty' body_ty).
  + apply typing_lam.
    * assumption.
    *

  apply typing_lam. apply IHHred.*)


apply HΣ in H. depelim H.  depelim Ht. apply typing_evar_entry.

Admitted.

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
