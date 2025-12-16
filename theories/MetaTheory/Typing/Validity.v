From Metaprog Require Import Prelude.
From Metaprog Require Export MetaTheory.Typing.SubstTyping.

(** This module proves two basic lemmas about the typing relation:
    - The validity lemma: in any typing derivation [Σ ;; Γ ⊢ t : T],
      [T] is itself well-typed.
    - Uniqueness of types (up to conversion).
*)

Lemma typing_lookup_context {s} Σ (Γ : context ∅ s) i :
  ctyping Σ Γ ->
  Σ ;; Γ ⊢ lookup_context i Γ : TType.
Proof.
intros H. induction H.
- depelim i.
- depelim i ; simp lookup_context ; simpl_subst.
  + change TType with (rename (@rshift s x) TType).
    eapply typing_rename ; eauto. apply typing_rshift. constructor ; auto.
  + change TType with (rename (@rshift s x) TType).
    eapply typing_rename ; eauto. apply typing_rshift. constructor ; auto.
Qed.

(***********************************************************************)
(** * Validity lemma. *)
(***********************************************************************)

(** The validity lemma for typing states that in any typing derivation,
    the type is well-typed. *)
Lemma typing_validity {s} Σ Γ (t T : term s) :
  typing_evar_map Σ ->
  Σ ;; Γ ⊢ t : T ->
  Σ ;; Γ ⊢ T : TType.
Proof.
intros HΣ H. induction H.
- constructor. revert H. apply All_context_consequence. firstorder.
- subst. apply typing_lookup_context. revert H.
  apply All_context_consequence. firstorder.
- constructor ; auto.
- constructor. eapply typing_context_validity ; eauto.
- assert (H1 : All_spine Σ (fun t T => Σ ;; Γ ⊢ t : T /\ Σ ;; Γ ⊢ T : TType) f_ty args T).
  { revert H0. apply All_spine_consequence. firstorder. }
  clear H H0. induction H1.
  + assumption.
  + apply IHAll_spine. destruct H as (H & _). apply typing_prod_inv in H.
    destruct H as (_ & Ha & Hb). change TType with (TType[x := arg]).
    eapply typing_substitute ; eauto. apply typing_scons.
    * assumption.
    * simpl_subst. apply H1.
    * apply typing_sid. eapply typing_context_validity ; eauto.
- simpl_subst. change TType with (@rename ∅ s wk_idx TType). eapply typing_rename.
  + apply typing_evar_type. now apply (HΣ ev).
  + split3.
    * constructor.
    * revert H. apply All_context_consequence. firstorder.
    * intros i. depelim i.
- assumption.
Qed.

(***********************************************************************)
(** * Uniqueness of types. *)
(***********************************************************************)

(** Types are unique (up to convertibility). This lemma will no longer be true
    once we add subtyping (with universes). *)
Lemma typing_unique_type {s} Σ Γ (t A A' : term s) :
  Σ ;; Γ ⊢ t : A ->
  Σ ;; Γ ⊢ t : A' ->
  Σ ⊢ A ≡ A'.
Proof.
intros HA. revert A'. induction HA ; intros A' HA'.
- apply typing_type_inv in HA'. now symmetry.
- subst. apply typing_var_inv in HA'. now symmetry.
- apply typing_lam_inv in HA'. destruct HA' as (body_ty' & HA' & Hty & Hbody).
  rewrite HA'. f_equiv. apply IHHA2. assumption.
- apply typing_prod_inv in HA'. now symmetry.
- apply typing_app_inv in HA'. destruct HA' as (f_ty' & T' & Hf' & Hspine & H1).
  apply IHHA in Hf'. rewrite <-H1.
  assert (H2 : All_spine Σ (typing Σ Γ) f_ty args T).
  { revert H. apply All_spine_consequence. firstorder. }
  clear A' H1 IHHA H HA. induction args in f_ty, f_ty', Hf', Hspine, H2 |- *.
  + depelim Hspine ; depelim H2. assumption.
  + depelim Hspine ; depelim H2. eapply IHargs ; [| eassumption.. ].
    assert (x0 = x) as ->. { destruct x0 ; destruct x ; reflexivity. }
    f_equiv. rewrite H0, H3 in Hf'. now apply conv_prod_inv in Hf'.
- apply typing_evar_inv in HA'. destruct HA' as (entry' & Hentry & HA').
  rewrite H0 in Hentry. depelim Hentry. now symmetry.
- rewrite <-H. now apply IHHA1.
Qed.