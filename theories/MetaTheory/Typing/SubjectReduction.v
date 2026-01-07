From Metaprog Require Import Prelude.
From Metaprog Require Export MetaTheory.Typing.Validity.

(** This module proves the subject reduction (aka preservation) lemma:
    reducing a well-typed term doesn't change its type.

    We also prove immediate consequences of this:
    - [typing] is compatible with reduction in contexts, terms and types.
    - [ctyping] is compatible with context reduction.
    - [rtyping] is compatible with context reduction.
    - [styping] is compatible with context reduction and substitution reduction.
*)

(** In a spine typing judgement, if the function type [f_ty] is well-typed
    than so is the result type [T]. *)
Lemma typing_spine_validity {Σ s} Γ (f_ty : term s) args T :
  All_spine Σ (typing Σ Γ) f_ty args T ->
  Σ ;; Γ ⊢ f_ty : TType ->
  Σ ;; Γ ⊢ T : TType.
Proof.
intros Hspine Hf. induction Hspine.
- assumption.
- apply typing_prod_inv in H. apply IHHspine.
  change TType with (TType[x := arg]). eapply typing_substitute.
  + apply H.
  + apply typing_scons.
    * apply H.
    * simpl_subst. assumption.
    * apply typing_sid. eapply typing_context_validity ; eauto.
Qed.

(***********************************************************************)
(** * Technical meat of the proof. *)
(***********************************************************************)

Section SubjectReduction.
Context (Σ : evar_map) (HΣ : typing_evar_map Σ).

(** Given a typing derivation [Σ ;; Γ ⊢ t : T], we prove at the same time that:
    - One reduction step in the term [t] preserves the type.
    - One reduction step in the context [Γ] preserves the type.

    This corresponds exactly to the property [sr_prop Γ t T].
    Our objective is then to show that [typing] implies [sr_prop].

    A technical detail is that we fix the reduction flags to [red_flags_all]
    in [sr_prop]: as a second (easy) step we prove that we can in fact
    reduce using any reduction flags. *)
Definition sr_prop {s} Γ (t T : term s) :=
  (forall t', Σ ⊢ t ~> t' -> Σ ;; Γ ⊢ t' : T) /\
  (forall Γ', cred1 red_flags_all Σ Γ Γ' -> Σ ;; Γ' ⊢ t : T).

Lemma ctyping_red1 {s} (Γ Γ' : context ∅ s) :
  All_context (@sr_prop) Γ ->
  cred1 red_flags_all Σ Γ Γ' ->
  ctyping Σ Γ ->
  ctyping Σ Γ'.
Proof.
intros Hsr Hred HΓ. induction Hred.
- constructor.
  + now depelim HΓ.
  + depelim HΓ. depelim Hsr. now apply H.
- constructor.
  + apply IHHred.
    * now depelim Hsr.
    * now depelim HΓ.
  + depelim Hsr. apply H ; auto.
Qed.

Lemma typing_lookup_context_red1 {s} (Γ Γ' : context ∅ s) i :
  All_context (@sr_prop) Γ ->
  ctyping Σ Γ ->
  cred1 red_flags_all Σ Γ Γ' ->
  Σ ;; Γ' ⊢ lookup_context i Γ : TType.
Proof.
intros Hsr HΓ Hred. induction Hred.
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
      --apply ctyping_red1 with Γ ; auto.
      --now apply H.
  + change TType with (rename (@rshift s x) TType). apply typing_rename with Γ' ; auto.
    apply typing_rshift. constructor ; auto.
    --apply ctyping_red1 with Γ ; auto.
    --now apply H.
Qed.

Lemma typing_spine_red1 {s} (Γ : context ∅ s) f_ty args args' T :
  All_spine Σ (fun t T => Σ ;; Γ ⊢ t : T /\ sr_prop Γ t T) f_ty args T ->
  All2 (fun a a' => Σ ⊢ a ~> a' \/ a = a') args args' ->
  exists T',
    All_spine Σ (typing Σ Γ) f_ty args' T' /\
    Σ ⊢ T ≡ T'.
Proof.
intros Hspine Hred. revert f_ty T Hspine. induction Hred ; intros f_ty T Hspine.
- depelim Hspine. exists f_ty. split ; [constructor | reflexivity].
- depelim Hspine. destruct H0 as (H0 & H0'). destruct H as [H | ->].
  + destruct (IHHred _ _ Hspine) as (T' & HT' & Hconv).
    apply All_spine_conv_func_type with (f_ty' := b[x0 := y]) in HT'.
    * destruct HT' as (T'' & HT' & HT''). exists T''. split.
      --econstructor ; eauto. now apply H2.
      --now rewrite Hconv.
    * f_equiv. f_equiv. now apply conv_of_red1.
  + destruct (IHHred _ _ Hspine) as (T' & HT' & Hconv).
    apply All_spine_conv_func_type with (f_ty' := b[x0 := y]) in HT'.
    * destruct HT' as (T'' & HT' & HT''). exists T''. split.
      --econstructor ; eauto. now destruct H2.
      --now rewrite Hconv.
    * reflexivity.
Qed.

Lemma OneOne2_red1_All2 {s} (xs ys : list (term s)) :
  OnOne2 (red1 red_flags_all Σ) xs ys ->
  All2 (fun x y => Σ ⊢ x ~> y \/ x = y) xs ys.
Proof.
intros H. induction H ; constructor ; auto.
apply All2_Reflexive. intros z. now right.
Qed.

(** The beta reduction rule preserves typing. *)
Lemma typing_beta {s} Γ x ty body arg args (T : term s) :
  Σ ;; Γ ⊢ TApp (TLam x ty body) (arg :: args) : T ->
  Σ ;; Γ ⊢ TApp (body[x := arg]) args : T.
Proof.
intros H. pose proof (HT := typing_validity _ _ _ HΣ H).
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

Lemma sr_prop_type {s} (Γ : context ∅ s) :
  ctyping Σ Γ -> All_context (@sr_prop) Γ ->
  sr_prop Γ TType TType.
Proof.
intros HΓ HΓ'. split.
- intros t' Hred. depelim Hred.
- intros Γ' Hred. constructor. apply ctyping_red1 with Γ ; auto.
Qed.

Lemma sr_prop_var {s} (Γ : context ∅ s) i :
  ctyping Σ Γ -> All_context (@sr_prop) Γ ->
  sr_prop Γ (TVar i) (lookup_context i Γ).
Proof.
intros HΓ HΓ'. split.
- intros t' Hred. depelim Hred.
- intros Γ' Hred. apply typing_conv_type with (lookup_context i Γ').
  + constructor ; auto. now apply ctyping_red1 with Γ.
  + apply lookup_context_cconv. symmetry. now apply cconv_of_cred1.
  + now apply typing_lookup_context_red1.
Qed.

Lemma sr_prop_lam {x s} (Γ : context ∅ s) ty body body_ty :
  Σ ;; Γ ⊢ ty : TType -> sr_prop Γ ty TType ->
  Σ ;; CCons Γ x ty ⊢ body : body_ty -> sr_prop (CCons Γ x ty) body body_ty ->
  sr_prop Γ (TLam x ty body) (TProd x ty body_ty).
Proof.
intros Hty Hty' Hbody Hbody'. split.
- intros t' Hred. depelim Hred.
  + apply typing_conv_type with (TProd x ty' body_ty).
    * constructor.
      --now apply Hty'.
      --apply Hbody' ; auto. now constructor.
    * now rewrite Hred.
    * constructor ; auto. eapply typing_validity ; eauto.
  + constructor ; auto. apply Hbody' ; auto.
- constructor.
  + now apply Hty'.
  + apply Hbody' ; auto. now constructor.
Qed.

Lemma sr_prop_prod {x s} (Γ : context ∅ s) a b :
  Σ ;; Γ ⊢ a : TType -> sr_prop Γ a TType ->
  Σ ;; CCons Γ x a ⊢ b : TType -> sr_prop (CCons Γ x a) b TType ->
  sr_prop Γ (TProd x a b) TType.
Proof.
intros Ha Ha' Hb Hb'. split.
- intros t' Hred. depelim Hred.
  + constructor.
    * now apply Ha'.
    * apply Hb'. now constructor.
  + constructor ; auto. apply Hb' ; auto.
- intros Γ' Hred. constructor.
  + now apply Ha'.
  + apply Hb'. now constructor.
Qed.

Lemma typing_nested_app {s} (Γ : context ∅ s) T0 T1 f args args' :
  Σ ;; Γ ⊢ TApp f args : T0 ->
  spine_typing Σ Γ T0 args' T1 ->
  Σ ;; Γ ⊢ TApp f (args ++ args') : T1.
Proof.
intros H Hargs'. pose proof (HT0 := H). apply typing_validity in HT0 ; try assumption.
apply typing_app_inv in H. destruct H as (f_ty & T0' & Hf & Hargs & Hconv).
pose proof (HT1 := Hargs'). apply typing_spine_validity in HT1 ; try assumption.
apply All_spine_conv_func_type with (f_ty' := T0') in Hargs' ; try easy.
clear T0 HT0 Hconv. destruct Hargs' as (T1' & Hargs' & Hconv).
apply typing_conv_type with T1' ; try easy. clear T1 HT1 Hconv.
apply typing_app with f_ty ; auto. now apply All_spine_app with T0'.
Qed.

Lemma sr_prop_app {s} (Γ : context ∅ s) f f_ty args T :
  Σ ;; Γ ⊢ f : f_ty -> sr_prop Γ f f_ty ->
  All_spine Σ (fun t T => Σ ;; Γ ⊢ t : T /\ sr_prop Γ t T) f_ty args T ->
  sr_prop Γ (TApp f args) T.
Proof.
intros Hf Hf' Hargs.
assert (Hargs' : spine_typing Σ Γ f_ty args T).
{ revert Hargs. apply All_spine_consequence. firstorder. }
split.
- intros t' Hred. depelim Hred.
  + eapply typing_beta ; eauto. apply typing_app with f_ty ; eauto.
  + depelim Hargs. assumption.
  + apply typing_nested_app with f_ty ; auto.
  + apply typing_app with f_ty ; [now apply Hf' |] ; auto.
  + assert (HT : Σ ;; Γ ⊢ T : TType).
    { eapply typing_spine_validity with f_ty args ; eauto using typing_validity. }
    apply typing_spine_red1 with (args' := args') in Hargs ; auto.
    2: now apply OneOne2_red1_All2.
    destruct Hargs as (T' & H' & Hconv). apply typing_conv_type with T'.
    * apply typing_app with f_ty ; auto.
    * now symmetry.
    * auto.
- intros Γ' Hred. apply typing_app with f_ty ; [now apply Hf' |].
  revert Hargs. apply All_spine_consequence. firstorder.
Qed.

Lemma sr_prop_evar {s} (Γ : context ∅ s) ev entry :
  Σ ev = Some entry ->
  ctyping Σ Γ -> All_context (@sr_prop) Γ ->
  sr_prop Γ (TEvar ev) (wk (evar_type entry)).
Proof.
intros Hev HΓ HΓ'. split.
- intros t' Hred. depelim Hred. rewrite H0 in Hev. depelim Hev. cbn.
  simpl_subst. eapply typing_rename.
  + apply HΣ in H0. depelim H0. eassumption.
  + split3 ; try easy. constructor.
- intros Γ' Hred. constructor ; auto. now apply ctyping_red1 with Γ.
Qed.

Lemma sr_prop_conv_type {s} Γ (t A B : term s) :
  Σ ;; Γ ⊢ t : A -> sr_prop Γ t A ->
  Σ ;; Γ ⊢ B : TType -> sr_prop Γ B TType ->
  Σ ⊢ A ≡ B ->
  sr_prop Γ t B.
Proof.
intros Ht Ht' HB HB' Hconv. split.
- intros t' Hred. apply typing_conv_type with A ; auto. now apply Ht'.
- intros Γ' Hred. apply typing_conv_type with A ; auto.
  + now apply Ht'.
  + now apply HB'.
Qed.

(** [typing] implies [sr_prop]. *)
Lemma sr_prop_all {s} Γ (t T : term s) :
  Σ ;; Γ ⊢ t : T ->
  sr_prop Γ t T.
Proof.
intros Ht. induction Ht.
- apply All_context_and in H. now apply sr_prop_type.
- apply All_context_and in H. subst. now apply sr_prop_var.
- now apply sr_prop_lam.
- now apply sr_prop_prod.
- now apply sr_prop_app with f_ty.
- apply All_context_and in H. now apply sr_prop_evar.
- now apply sr_prop_conv_type with A.
Qed.

End SubjectReduction.

(***********************************************************************)
(** * Compatibility of typing with one-step reduction. *)
(***********************************************************************)

Section TypingRed1.
  Context {flags : red_flags} {Σ : evar_map} {s : scope}.
  Hypothesis (HΣ : typing_evar_map Σ).

  (** One reduction step in the context preserves the typing derivation. *)
  Lemma typing_red1_context :
    Proper (cred1 flags Σ ==> eq ==> eq ==> Basics.impl) (@typing Σ s).
  Proof.
  intros Γ Γ' HΓ t t' <- T T' <- Htyp.
  pose proof (H := sr_prop_all Σ HΣ Γ t T Htyp). apply H.
  revert HΓ. apply cred1_extend_flags, red_flags_incl_all_r.
  Qed.

  (** One reduction step in the term preserves the typing derivation. *)
  Lemma typing_red1_term :
    Proper (eq ==> red1 flags Σ ==> eq ==> Basics.impl) (@typing Σ s).
  Proof.
  intros Γ Γ' <- t t' Ht T T' <- Htyp.
  pose proof (H := sr_prop_all Σ HΣ Γ t T Htyp). apply H.
  revert Ht. apply red1_extend_flags, red_flags_incl_all_r.
  Qed.

  (** One reduction step in the type preserves the typing derivation. *)
  Lemma typing_red1_type :
    Proper (eq ==> eq ==> red1 flags Σ ==> Basics.impl) (@typing Σ s).
  Proof.
  intros Γ Γ' <- t t' <- T T' HT Htyp.
  apply typing_conv_type with T.
  - assumption.
  - apply (red1_extend_flags (red_flags_incl_all_r _)) in HT.
    now rewrite HT.
  - eapply typing_red1_term ; eauto. now apply typing_validity in Htyp.
  Qed.

End TypingRed1.

(***********************************************************************)
(** * Compatibility of typing with multi-step reduction. *)
(***********************************************************************)

Section TypingRed.
  Context {flags : red_flags} {Σ : evar_map} {s : scope}.
  Hypothesis (HΣ : typing_evar_map Σ).

  Lemma typing_red_context :
    Proper (cred flags Σ ==> eq ==> eq ==> Basics.impl) (@typing Σ s).
  Proof.
  intros Γ Γ' HΓ t t' <- T T' <- Htyp. induction HΓ using cred_ind_alt.
  - assumption.
  - eapply typing_red1_context ; eauto.
  Qed.

  Lemma typing_red_term :
    Proper (eq ==> red flags Σ ==> eq ==> Basics.impl) (@typing Σ s).
  Proof.
  intros Γ Γ' <- t t' Ht T T' <- Htyp. induction Ht.
  - assumption.
  - eapply typing_red1_term ; eauto.
  Qed.

  Lemma typing_red_type :
    Proper (eq ==> eq ==> red flags Σ ==> Basics.impl) (@typing Σ s).
  Proof.
  intros Γ Γ' <- t t' <- T T' HT Htyp. induction HT.
  - assumption.
  - eapply typing_red1_type ; eauto.
  Qed.

  (** Reduction in the context, term, and type preserves the typing derivation. *)
  #[export] Instance typing_red :
    Proper (cred flags Σ ==> red flags Σ ==> red flags Σ ==> Basics.impl) (@typing Σ s).
  Proof.
  intros Γ Γ' HΓ t t' Ht T T' HT Htyp.
  enough (Σ ;; Γ ⊢ t' : T'). { revert H. apply typing_red_context ; auto. }
  enough (Σ ;; Γ ⊢ t : T'). { revert H. apply typing_red_term ; auto. }
  enough (Σ ;; Γ ⊢ t : T). { revert H. apply typing_red_type ; auto. }
  assumption.
  Qed.

End TypingRed.