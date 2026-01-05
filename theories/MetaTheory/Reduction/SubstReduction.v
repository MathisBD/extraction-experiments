From Metaprog Require Import Prelude.
From Metaprog Require Export MetaTheory.Reduction.TermReduction.

(** This module defines reduction of substitutions and proves some
    basic properties, notably compatibility of reduction with renaming
    and substitution.
*)

(***********************************************************************)
(** * Reduction on substitutions. *)
(***********************************************************************)

(** Reduction on substitutions is just pointwise reduction.

    We wrap the definition in a record because otherwise rewriting with
    [H : sred flags Σ σ σ'] will sometimes fail due to setoid rewrite
    wanting to rewrite [sapply σ i] into [sapply σ' i].  *)
Record sred flags Σ {s s'} (σ σ' : subst s s') := {
  sred_prop : forall i, Σ ⊢ sapply σ i ~~>{flags} sapply σ' i
}.

(***********************************************************************)
(** * Typeclass instances for setoid rewriting. *)
(***********************************************************************)

#[export] Instance sred_Reflexive flags Σ s s' : Reflexive (@sred flags Σ s s').
Proof. intros σ. constructor. reflexivity. Qed.

#[export] Instance sred_Transitive flags Σ s s' : Transitive (@sred flags Σ s s').
Proof.
intros σ1 σ2 σ3 [H1] [H2]. constructor. intros i. etransitivity ; eauto.
Qed.

#[export] Instance red_sapply flags Σ s s' :
  Proper (sred flags Σ ==> eq ==> red flags Σ) (@sapply s s').
Proof. intros σ σ' [Hσ] i ? <-. apply Hσ. Qed.

Lemma sred_extend_flags {flags1 flags2 Σ s s'} :
  red_flags_incl flags1 flags2 ->
  subrelation (@sred flags1 Σ s s') (@sred flags2 Σ s s').
Proof.
intros Hf σ1 σ2 [Hσ]. constructor. intros i.
eapply red_extend_flags ; eauto.
Qed.

(***********************************************************************)
(** * Compatibility of reduction with renaming and substitution. *)
(***********************************************************************)

Section Substitutivity.
  Context {flags : red_flags} {Σ : evar_map}.

  (** Compatibility of renaming with [red1]. *)
  #[export] Instance red1_rename {s s'} (ρ : ren s s') :
    Proper (red1 flags Σ ==> red1 flags Σ) (rename ρ).
  Proof.
  intros t t' H. induction H in s', ρ |- * ; simpl_subst.
  - cbn. apply red1_beta_alt ; auto. f_equal. now simpl_subst.
  - eapply red1_evar_expand ; auto. eassumption.
  - now apply red1_lam_l.
  - now apply red1_lam_r.
  - now apply red1_prod_l.
  - now apply red1_prod_r.
  - now apply red1_app_l.
  - apply red1_app_r, OnOne2_map. revert H. apply OnOne2_consequence. firstorder.
  Qed.

  (** Compatibility of renaming with [red]. *)
  #[export] Instance red_rename {s s'} (ρ : ren s s') :
    Proper (red flags Σ ==> red flags Σ) (rename ρ).
  Proof.
  intros t t' H. induction H.
  - reflexivity.
  - now rewrite IHred, H0.
  Qed.

  #[export] Instance red_scons {s s' x} :
    Proper (red flags Σ ==> sred flags Σ ==> sred flags Σ) (@scons s s' x).
  Proof.
  intros t t' Ht σ σ' Hσ. constructor. intros i. depelim i ; simpl_subst.
  - assumption.
  - now rewrite Hσ.
  Qed.

  #[export] Instance red_srcomp {s s' s''} :
    Proper (sred flags Σ ==> eq ==> sred flags Σ) (@srcomp s s' s'').
  Proof.
  intros σ σ' Hσ ρ ρ' <-. constructor. intros i. simpl_subst.
  now rewrite Hσ.
  Qed.

  #[export] Instance red_rscomp {s s' s''} ρ :
    Proper (sred flags Σ ==> sred flags Σ) (@rscomp s s' s'' ρ).
  Proof.
  intros σ σ' Hσ. constructor. intros i. simpl_subst.
  now rewrite Hσ.
  Qed.

  #[export] Instance red_sup {s s' x} :
    Proper (sred flags Σ ==> sred flags Σ) (@sup s s' x).
  Proof. intros σ σ' Hσ. unfold sup. now rewrite Hσ. Qed.

  (** Compatibility of substitution with [red1]. Note that a single reduction in
      the substitution can cause several reductions in the result, so here we fix
      the substitution [σ]. *)
  #[export] Instance red1_substitute_l {s s'} (σ : subst s s') :
    Proper (red1 flags Σ ==> red1 flags Σ) (substitute σ).
  Proof.
  intros t t' H. induction H in s', σ |- * ; simpl_subst.
  - cbn. apply red1_beta_alt ; [assumption|]. f_equal. now simpl_subst.
  - eapply red1_evar_expand ; [assumption|]. eassumption.
  - now apply red1_lam_l.
  - now apply red1_lam_r.
  - now apply red1_prod_l.
  - now apply red1_prod_r.
  - now apply red1_app_l.
  - apply red1_app_r, OnOne2_map. revert H. apply OnOne2_consequence. firstorder.
  Qed.

  (** Substitution lemma for [red]. *)
  #[export] Instance red_substitute {s s'} :
    Proper (sred flags Σ ==> red flags Σ ==> red flags Σ) (@substitute s s').
  Proof.
  intros σ σ' Hσ t t' H. transitivity (substitute σ' t).
  - clear t' H. induction t in s', σ, σ', Hσ |- * using term_ind' ; simpl_subst.
    + reflexivity.
    + now rewrite Hσ.
    + f_equiv.
      * now apply IHt1.
      * apply IHt2. now f_equiv.
    + f_equiv.
      * now apply IHt1.
      * apply IHt2. now f_equiv.
    + f_equiv.
      * now apply IHt.
      * clear t IHt. induction H ; cbn ; constructor ; auto.
    + reflexivity.
  - induction H.
    + reflexivity.
    + now rewrite IHred, H0.
  Qed.

  #[export] Instance red_scomp {s s' s''} :
    Proper (sred flags Σ ==> sred flags Σ ==> sred flags Σ) (@scomp s s' s'').
  Proof.
  intros σ σ' Hσ τ τ' Hτ. constructor. intros i. simpl_subst.
  now rewrite Hτ, Hσ.
  Qed.

End Substitutivity.