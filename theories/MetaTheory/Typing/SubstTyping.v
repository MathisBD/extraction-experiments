From Metaprog Require Import Prelude.
From Metaprog Require Export MetaTheory.Typing.EvarMapTyping.

(** This module defines a notion of typing for renamings and substitutions,
    and proves the compatibility of typing with renaming and substitution. *)

(***********************************************************************)
(** * Typing renamings. *)
(***********************************************************************)

(** [Σ ;; Γ ⊢ᵣ ρ : Δ] means that the renaming [ρ] maps well-typed terms
    in context [Γ] to well-typed terms in context [Δ]. *)
Definition rtyping (Σ : evar_map) {s s'} (Γ : context ∅ s) (ρ : ren s s') (Δ : context ∅ s') :=
  ctyping Σ Γ /\
  ctyping Σ Δ /\
  forall i, rename ρ (lookup_context i Γ) = lookup_context (rapply ρ i) Δ.

Notation "Σ ;; Γ ⊢ᵣ ρ : Δ" := (rtyping Σ Γ ρ Δ)
  (at level 50, Γ at next level, ρ at next level, Δ at next level).

Lemma rtyping_extend_evm {Σ1 Σ2 s s' Γ Δ} {ρ : ren s s'} :
  Σ1 ⊑ Σ2 ->
  rtyping Σ1 Γ ρ Δ ->
  rtyping Σ2 Γ ρ Δ.
Proof.
intros HΣ (HΓ & HΔ & Hρ). split3.
- now apply (ctyping_extend_evm HΣ).
- now apply (ctyping_extend_evm HΣ).
- assumption.
Qed.

(***********************************************************************)
(** * Typing substitutions. *)
(***********************************************************************)

(** [Σ ;; Γ ⊢ₛ σ : Δ] means that the substitution [σ] maps well-typed
    terms in context [Γ] to well-typed terms in context [Δ]. *)
Definition styping (Σ : evar_map) {s s'} (Γ : context ∅ s) (σ : subst s s') (Δ : context ∅ s') :=
  ctyping Σ Γ /\
  ctyping Σ Δ /\
  forall i, Σ ;; Δ ⊢ sapply σ i : substitute σ (lookup_context i Γ).

Notation "Σ ;; Γ ⊢ₛ σ : Δ" := (styping Σ Γ σ Δ)
  (at level 50, Γ at next level, σ at next level, Δ at next level).

Lemma styping_extend_evm {Σ1 Σ2 s s' Γ Δ} {σ : subst s s'} :
  Σ1 ⊑ Σ2 ->
  styping Σ1 Γ σ Δ ->
  styping Σ2 Γ σ Δ.
Proof.
intros HΣ (HΓ & HΔ & Hσ). split3.
- now apply (ctyping_extend_evm HΣ).
- now apply (ctyping_extend_evm HΣ).
- intros i. now apply (typing_extend_evm HΣ).
Qed.

(***********************************************************************)
(** * Compatibility of typing with renaming. *)
(***********************************************************************)

Lemma typing_rid {s} Σ (Γ : context ∅ s) :
  ctyping Σ Γ ->
  Σ ;; Γ ⊢ᵣ rid : Γ.
Proof. intros H. split3 ; auto. intros i. simpl_subst. reflexivity. Qed.

Lemma typing_rshift {s x} Σ (Γ : context ∅ s) ty :
  ctyping Σ (CCons Γ x ty) ->
  Σ ;; Γ ⊢ᵣ rshift : CCons Γ x ty.
Proof.
intros H. split3 ; auto. now depelim H.
Qed.

Lemma typing_rcons {s s' x} Σ (Γ : context ∅ s) (Δ : context ∅ s') i ρ ty :
  Σ ;; Γ ⊢ ty : TType ->
  rename ρ ty = lookup_context i Δ ->
  Σ ;; Γ ⊢ᵣ ρ : Δ ->
  Σ ;; CCons Γ x ty ⊢ᵣ rcons x i ρ : Δ.
Proof.
intros H1 H2 H3. split3.
- constructor.
  + apply H3.
  + apply H1.
- apply H3.
- intros j. depelim j ; simpl_subst ; simp lookup_context ; simpl_subst.
  + assumption.
  + apply H3.
Qed.

Lemma typing_rcomp {s s' s''} Σ Γ Δ E (ρ1 : ren s s') (ρ2 : ren s' s'') :
  Σ ;; Γ ⊢ᵣ ρ1 : Δ ->
  Σ ;; Δ ⊢ᵣ ρ2 : E ->
  Σ ;; Γ ⊢ᵣ rcomp ρ1 ρ2 : E.
Proof.
intros H1 H2. split3.
- apply H1.
- apply H2.
- intros i. simpl_subst. rewrite <-rename_rename.
  destruct H1 as (_ & _ & H1). rewrite H1.
  destruct H2 as (_ & _ & H2). rewrite H2.
  reflexivity.
Qed.

Lemma typing_rup {s s' x} Σ Γ Δ (ρ : ren s s') ty :
  Σ ;; Γ ⊢ ty : TType ->
  Σ ;; Δ ⊢ rename ρ ty : TType ->
  Σ ;; Γ ⊢ᵣ ρ : Δ ->
  Σ ;; CCons Γ x ty ⊢ᵣ rup x ρ : CCons Δ x (rename ρ ty).
Proof.
intros H1 H2 H3. unfold rup. apply typing_rcons.
- assumption.
- simp lookup_context. now simpl_subst.
- eapply typing_rcomp ; eauto. apply typing_rshift. constructor.
  + apply H3.
  + apply H2.
Qed.

(** Compatibility of typing with renaming. *)
Lemma typing_rename {s s'} Σ Γ Δ (ρ : ren s s') t T :
  Σ ;; Γ ⊢ t : T ->
  Σ ;; Γ ⊢ᵣ ρ : Δ ->
  Σ ;; Δ ⊢ rename ρ t : rename ρ T.
Proof.
intros Ht Hρ. induction Ht in s', ρ, Δ, Hρ |- * ; simpl_subst.
- apply typing_type. apply Hρ.
- subst. destruct Hρ as (Hρ1 & Hρ2 & Hρ3). rewrite Hρ3. constructor ; auto.
- apply typing_lam ; auto using typing_rup.
- apply typing_prod ; auto using typing_rup.
- eapply typing_app.
  + now apply IHHt.
  + clear IHHt Ht. depind H ; cbn ; [constructor ; now rewrite H |].
    apply All_spine_cons with (x := x) (a := rename ρ a) (b := rename (rup x ρ) b).
    * simpl_subst in H. now apply H.
    * rewrite H0. simpl_subst. reflexivity.
    * now apply H1.
    * simpl_subst. simpl_subst in IHAll_spine. apply IHAll_spine ; auto.
- eapply typing_evar ; eauto. apply Hρ.
- apply typing_conv_type with (A := rename ρ A) ; auto. now rewrite H.
Qed.

(***********************************************************************)
(** * Compatibility of typing with substitution. *)
(***********************************************************************)

Lemma typing_sid {s} Σ (Γ : context ∅ s) :
  ctyping Σ Γ ->
  Σ ;; Γ ⊢ₛ sid : Γ.
Proof. intros H. split3 ; auto. intros i. simpl_subst. now constructor. Qed.

Lemma typing_sshift {s x} Σ (Γ : context ∅ s) ty :
  ctyping Σ (CCons Γ x ty) ->
  Σ ;; Γ ⊢ₛ sshift : CCons Γ x ty.
Proof.
intros H. split3 ; auto.
- now depelim H.
- simpl_subst. constructor ; auto.
Qed.

Lemma typing_scons {s s' x} Σ (Γ : context ∅ s) (Δ : context ∅ s') t σ ty :
  Σ ;; Γ ⊢ ty : TType ->
  Σ ;; Δ ⊢ t : substitute σ ty ->
  Σ ;; Γ ⊢ₛ σ : Δ ->
  Σ ;; CCons Γ x ty ⊢ₛ scons x t σ : Δ.
Proof.
intros H1 H2 H3. split3.
- constructor ; auto. apply H3.
- apply H3.
- intros i. depelim i ; simpl_subst ; simp lookup_context.
  + simpl_subst. assumption.
  + simpl_subst. destruct H3 as (HΔ & HΓ & H3). apply H3.
Qed.

Lemma typing_srcomp {s s' s''} Σ Γ Δ E (σ : subst s s') (ρ : ren s' s'') :
  Σ ;; Γ ⊢ₛ σ : Δ ->
  Σ ;; Δ ⊢ᵣ ρ : E ->
  Σ ;; Γ ⊢ₛ srcomp σ ρ : E.
Proof.
intros H1 H2. split3.
- apply H1.
- apply H2.
- intros i. simpl_subst. rewrite <-rename_substitute.
  eapply typing_rename ; [|eassumption]. apply H1.
Qed.

Lemma typing_sup {s s' x} Σ Γ Δ (σ : subst s s') ty :
  Σ ;; Γ ⊢ ty : TType ->
  Σ ;; Δ ⊢ substitute σ ty : TType ->
  Σ ;; Γ ⊢ₛ σ : Δ ->
  Σ ;; CCons Γ x ty ⊢ₛ sup x σ : CCons Δ x (substitute σ ty).
Proof.
intros H1 H2 H3. unfold sup. apply typing_scons.
- apply H1.
- constructor.
  + constructor ; auto. apply H3.
  + simp lookup_context. simpl_subst. reflexivity.
- eapply typing_srcomp ; eauto. apply typing_rshift. constructor ; auto. apply H3.
Qed.

Lemma typing_substitute {s s'} Σ Γ Δ (σ : subst s s') t T :
  Σ ;; Γ ⊢ t : T ->
  Σ ;; Γ ⊢ₛ σ : Δ ->
  Σ ;; Δ ⊢ substitute σ t : substitute σ T.
Proof.
intros Ht Hσ. induction Ht in s', σ, Δ, Hσ |- * ; simpl_subst.
- constructor. apply Hσ.
- subst. apply Hσ.
- apply typing_lam ; auto using typing_sup.
- apply typing_prod ; auto using typing_sup.
- apply typing_app with (f_ty := substitute σ f_ty) ; auto.
  clear f Ht IHHt. depind H ; [constructor ; now rewrite H |]. cbn.
  apply All_spine_cons with (x := x) (a := substitute σ a) (b := substitute (sup x σ) b).
  + simpl_subst in H. now apply H.
  + rewrite H0. simpl_subst. reflexivity.
  + now apply H1.
  + simpl_subst. simpl_subst in IHAll_spine. now apply IHAll_spine.
- econstructor ; eauto. apply Hσ.
- eapply typing_conv_type ; eauto. now rewrite H.
Qed.

Lemma typing_rscomp {s s' s''} Σ Γ Δ E (ρ : ren s s') (σ : subst s' s'') :
  Σ ;; Γ ⊢ᵣ ρ : Δ ->
  Σ ;; Δ ⊢ₛ σ : E ->
  Σ ;; Γ ⊢ₛ rscomp ρ σ : E.
Proof.
intros H1 H2. split3.
- apply H1.
- apply H2.
- intros i. rewrite <-substitute_rename.
  assert (sapply (rscomp ρ σ) i = substitute σ (TVar (rapply ρ i))) as -> by now simpl_subst.
  eapply typing_substitute ; eauto. destruct H1 as (_ & _ & H1). rewrite H1.
  constructor ; auto. apply H2.
Qed.

Lemma typing_scomp {s s' s''} Σ Γ Δ E (σ1 : subst s s') (σ2 : subst s' s'') :
  Σ ;; Γ ⊢ₛ σ1 : Δ ->
  Σ ;; Δ ⊢ₛ σ2 : E ->
  Σ ;; Γ ⊢ₛ scomp σ1 σ2 : E.
Proof.
intros H1 H2. split3.
- apply H1.
- apply H2.
- intros i. simpl_subst. rewrite <-substitute_substitute.
  eapply typing_substitute ; eauto. apply H1.
Qed.
