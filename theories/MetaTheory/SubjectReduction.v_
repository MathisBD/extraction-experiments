From Metaprog Require Import Prelude.
From Metaprog Require Export MetaTheory.Typing.

(** This module proves the subject reduction (aka preservation) lemma:
    reducing a well-typed term doesn't change its type. *)

(** Beta reduction preserves typing. *)
Lemma typing_beta {s} Σ Γ x ty body arg args (T : term s) :
  typing_evar_map Σ ->
  Σ ;; Γ ⊢ TApp (TLam x ty body) (arg :: args) : T ->
  Σ ;; Γ ⊢ TApp (body[x := arg]) args : T.
Proof.
intros HΣ H. pose proof (HT := typing_validity _ _ _ _ HΣ H).
apply typing_app_inv in H. destruct H as (f_ty & T' & H1 & H2 & H3).
apply typing_conv_type with T' ; [|assumption..]. clear T H3 HT.

apply typing_lam_inv in H1. destruct H1 as (body_ty & H1 & Hty & Hbody).
depelim H2. assert (x0 = x) as ->. { destruct x0 ; destruct x ; reflexivity. }
rewrite H0 in H1. apply conv_prod_inv in H1. clear f_ty H0. destruct H1 as (Ha & Hb).

assert (Hbody' : Σ ;; Γ ⊢ body[x := arg] : body_ty[x := arg]).
{
  apply typing_substitute with (CCons Γ x ty) ; [assumption|].
  apply typing_scons.
  - assumption.
  - simpl_subst. apply typing_conv_type with a ; auto.
  - apply typing_sid. eapply typing_context_validity ; eauto.
}

assert (Hbody'' : Σ ;; Γ ⊢ body[x := arg] : b[x := arg]).
{
  apply typing_conv_type with (body_ty[x := arg]) ; [assumption | |].
  - now rewrite Hb.
  - change TType with (TType[x := arg]). eapply typing_substitute with (CCons Γ x a).
    + apply typing_prod_inv in H. apply H.
    + apply typing_scons.
      * eapply typing_validity ; eassumption.
      * simpl_subst. assumption.
      * apply typing_sid. eapply typing_context_validity ; eauto.
}
eapply typing_app ; eauto.
Qed.

(** Evar expansion preserves typing. *)
Lemma typing_evar_expand {s} Σ Γ ev ty def (T : term s) :
  typing_evar_map Σ ->
  Σ ;; Γ ⊢ TEvar ev : T ->
  Σ ev = Some (mk_evar_entry ty (Some def)) ->
  Σ ;; Γ ⊢ wk def : T.
Proof.
intros HΣ Hev Hentry. apply typing_conv_type with (wk ty).
- simpl_subst. apply typing_rename with CNil.
  + apply HΣ in Hentry. depelim Hentry. assumption.
  + split3.
    * constructor.
    * eapply typing_context_validity ; eassumption.
    * intros i. depelim i.
- apply typing_evar_inv in Hev. destruct Hev as (entry & H & HT).
  rewrite H in Hentry. depelim Hentry. cbn in HT. now symmetry.
- eapply typing_validity ; eassumption.
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


Definition sr_prop Σ {s} Γ (t T : term s) :=
  typing_evar_map Σ ->
    (forall t', Σ ⊢ t ~> t' -> Σ ;; Γ ⊢ t' : T) /\
    (forall Γ', Σ ⊢ Γ ~>ctx Γ' -> Σ ;; Γ' ⊢ t : T).

Lemma All_context_and (P Q : forall s, context ∅ s -> term s -> term s -> Prop) s (Γ : context ∅ s) :
  All_context (fun s Γ t T => P s Γ t T /\ Q s Γ t T) Γ <->
  (All_context P Γ /\ All_context Q Γ).
Proof.
induction Γ.
- split ; constructor ; constructor.
- split.
  + intros H. depelim H. rewrite IHΓ in H. split ; now constructor.
  + intros (H1 & H2). depelim H1. depelim H2. constructor.
    * now rewrite IHΓ.
    * now split.
Qed.

Lemma red1_context_conv_lookup {s} Σ (Γ Γ' : context ∅ s) i :
  Σ ⊢ Γ ~>ctx Γ' ->
  Σ ⊢ lookup_context i Γ ≡ lookup_context i Γ'.
Proof.
intros Hred. induction Hred ; depelim i ; simp lookup_context ; simpl_subst.
- now rewrite H.
- reflexivity.
- reflexivity.
- now rewrite IHHred.
Qed.

Lemma typing_context_red1 {s} Σ (Γ Γ' : context ∅ s) :
  typing_evar_map Σ ->
  All_context (@sr_prop Σ) Γ ->
  Σ ⊢ Γ ~>ctx Γ' ->
  typing_context Σ Γ ->
  typing_context Σ Γ'.
Proof.
intros HΣ Hsr Hred HΓ. induction Hred.
- constructor.
  + now depelim HΓ.
  + depelim HΓ. depelim Hsr. now apply H.
- constructor.
  + apply IHHred.
    * now depelim Hsr.
    * now depelim HΓ.
  + depelim Hsr. apply H ; auto.
Qed.

Lemma typing_lookup_context_red1 {s} Σ (Γ Γ' : context ∅ s) i :
  typing_evar_map Σ ->
  All_context (@sr_prop Σ) Γ ->
  typing_context Σ Γ ->
  Σ ⊢ Γ ~>ctx Γ' ->
  Σ ;; Γ' ⊢ lookup_context i Γ : TType.
Proof.
intros HΣ Hsr HΓ Hred. induction Hred.
- depelim Hsr. depelim HΓ. depelim i ; simp lookup_context ; simpl_subst.
  + change TType with (rename (@rshift s x) TType). apply typing_rename with Γ ; auto.
    apply typing_rshift. constructor ; auto. now apply H.
  + change TType with (rename (@rshift s x) TType). apply typing_rename with Γ.
    * now apply typing_lookup_context.
    * apply typing_rshift. constructor ; auto. now apply H.
- depelim Hsr. depelim HΓ. depelim i ; simp lookup_context ; simpl_subst.
  + change TType with (rename (@rshift s x) TType). apply typing_rename with Γ' ; auto.
    * now apply H.
    * apply typing_rshift. constructor ; auto.
      --apply typing_context_red1 with Γ ; auto.
      --now apply H.
  + change TType with (rename (@rshift s x) TType). apply typing_rename with Γ' ; auto.
    apply typing_rshift. constructor ; auto.
    --apply typing_context_red1 with Γ ; auto.
    --now apply H.
Qed.

(** In [All_spine Σ P f_ty args T] we can change the function type [f_ty]
    to a convertible one, as long as we are willing to accept that the return
    type [T] also changes to a convertible one. *)
Lemma All_spine_conv_func_type {s} Σ P f_ty f_ty' args (T : term s) :
  All_spine Σ P f_ty args T ->
  Σ ⊢ f_ty ≡ f_ty' ->
  exists T',
    All_spine Σ P f_ty' args T' /\
    Σ ⊢ T ≡ T'.
Proof.
intros Hspine Hconv. induction Hspine in f_ty', Hconv |- *.
- exists f_ty'. split ; [constructor | assumption].
- specialize (IHHspine (b[x := arg])). forward IHHspine by reflexivity.
  destruct IHHspine as (T' & Hspine' & HconvT).
  exists T'. split ; auto. econstructor ; eauto. now rewrite <-Hconv.
Qed.

Lemma typing_spine_red1 {s} Σ (Γ : context ∅ s) f_ty args args' T :
  typing_evar_map Σ ->
  All_spine Σ (fun t T => Σ ;; Γ ⊢ t : T /\ sr_prop Σ Γ t T) f_ty args T ->
  All2 (fun a a' => Σ ⊢ a ~> a' \/ a = a') args args' ->
  exists T',
    All_spine Σ (typing Σ Γ) f_ty args' T' /\
    Σ ⊢ T ≡ T'.
Proof.
intros HΣ Hspine Hred. revert f_ty T Hspine. induction Hred ; intros f_ty T Hspine.
- depelim Hspine. exists f_ty. split ; [constructor | reflexivity].
- depelim Hspine. destruct H0 as (H0 & H0'). destruct H as [H | ->].
  + destruct (IHHred _ _ Hspine) as (T' & HT' & Hconv).
    apply All_spine_conv_func_type with (f_ty' := b[x0 := y]) in HT'.
    * destruct HT' as (T'' & HT' & HT''). exists T''. split.
      --econstructor ; eauto. now apply H2.
      --now rewrite Hconv.
    * admit.
  + destruct (IHHred _ _ Hspine) as (T' & HT' & Hconv).
    apply All_spine_conv_func_type with (f_ty' := b[x0 := y]) in HT'.
    * destruct HT' as (T'' & HT' & HT''). exists T''. split.
      --econstructor ; eauto. now destruct H2.
      --now rewrite Hconv.
    * reflexivity.
Admitted.

(** One-step reduction preserves typing. *)
Lemma typing_red1 {s} Σ Γ (t T : term s) :
  Σ ;; Γ ⊢ t : T ->
  sr_prop Σ Γ t T.
Proof.
intros Ht. induction Ht ; (split ; [intros t' Hred | intros Γ' Hred]).
- depelim Hred.
- constructor. rewrite All_context_and in H. now apply typing_context_red1 with Γ.
- depelim Hred.
- subst. rewrite All_context_and in H. apply typing_conv_type with (lookup_context i Γ').
  + constructor.
    * now apply typing_context_red1 with Γ.
    * reflexivity.
  + symmetry. now apply red1_context_conv_lookup.
  + now apply typing_lookup_context_red1.
- depelim Hred.
  + apply typing_conv_type with (TProd x ty' body_ty).
    * constructor.
      --now apply IHHt1.
      --apply IHHt2 ; auto ; now constructor.
    * now rewrite Hred.
    * constructor ; auto. eapply typing_validity ; eauto.
  + constructor ; auto. apply IHHt2 ; auto.
- constructor.
  + now apply IHHt1.
  + apply IHHt2 ; auto ; now constructor.
- depelim Hred.
  + constructor.
    * apply IHHt1 ; auto.
    * apply IHHt2 ; auto ; now constructor.
  + constructor ; auto. apply IHHt2 ; auto.
- constructor.
  + now apply IHHt1.
  + apply IHHt2 ; auto ; now constructor.
- depelim Hred.
  + eapply typing_beta ; eauto. apply typing_app with f_ty ; eauto.
    revert H. apply All_spine_consequence. firstorder.
  + apply typing_app with f_ty ; [now apply IHHt |].
    revert H. apply All_spine_consequence. firstorder.
  + apply typing_app with f_ty ; [assumption |].
    clear f IHHt Ht. revert args' H1. induction H ; intros args' Hone. ; depelim Hone.
    * econstructor ; eauto.
      --now destruct H.
      --apply H2 ; auto.
      --admit.
    * econstructor ; eauto.
      --now destruct H.
      --now destruct H2.
- apply typing_app with f_ty ; [now apply IHHt |].
  clear f Ht IHHt. induction H ; econstructor ; try eassumption.
  + apply H ; auto.
  + apply H2 ; auto.
- depelim Hred. rewrite H0 in H2. depelim H2. cbn. simpl_subst. eapply typing_rename.
  + apply H1 in H0. depelim H0. eassumption.
  + split3.
    * constructor.
    * revert H. apply All_context_consequence. firstorder.
    * intros i. depelim i.
- constructor ; auto. rewrite All_context_and in H. now apply typing_context_red1 with Γ.
- apply typing_conv_type with A ; auto. now apply IHHt1.
- apply typing_conv_type with A ; auto.
  + now apply IHHt1.
  + now apply IHHt2.
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
