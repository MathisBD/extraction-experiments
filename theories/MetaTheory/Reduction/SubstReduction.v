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
    [H : sred Σ σ σ'] will sometimes fail due to setoid rewrite wanting to rewrite
    [sapply σ i] into [sapply σ' i].  *)
Record sred {s s'} Σ (σ σ' : subst s s') := {
  sred_prop : forall i, Σ ⊢ sapply σ i ~~> sapply σ' i
}.

#[export] Instance sred_Reflexive s s' Σ : Reflexive (@sred s s' Σ).
Proof. intros σ. constructor. reflexivity. Qed.

#[export] Instance sred_Transitive s s' Σ : Transitive (@sred s s' Σ).
Proof.
intros σ1 σ2 σ3 [H1] [H2]. constructor. intros i. etransitivity ; eauto.
Qed.

#[export] Instance red_sapply {s s'} Σ :
  Proper (sred Σ ==> eq ==> red Σ) (@sapply s s').
Proof. intros σ σ' [Hσ] i ? <-. apply Hσ. Qed.

(***********************************************************************)
(** * Compatibility of reduction with renaming. *)
(***********************************************************************)

(** Compatibility of renaming with [red1]. *)
#[export] Instance red1_rename {Σ s s'} (ρ : ren s s') :
  Proper (red1 Σ ==> red1 Σ) (rename ρ).
Proof.
intros t t' H. induction H in s', ρ |- * ; simpl_subst.
- cbn. apply red1_beta_alt. f_equal. now simpl_subst.
- eapply red1_evar_expand. eassumption.
- now apply red1_lam_l.
- now apply red1_lam_r.
- now apply red1_prod_l.
- now apply red1_prod_r.
- now apply red1_app_l.
- apply red1_app_r, OnOne2_map. revert H. apply OnOne2_consequence. firstorder.
Qed.

(** Compatibility of renaming with [red]. *)
#[export] Instance red_rename {Σ s s'} (ρ : ren s s') :
  Proper (red Σ ==> red Σ) (rename ρ).
Proof.
intros t t' H. induction H.
- reflexivity.
- now rewrite IHred, H0.
Qed.

(***********************************************************************)
(** * Compatibility of reduction with substitution. *)
(***********************************************************************)

#[export] Instance red_scons {Σ s s' x} :
  Proper (red Σ ==> sred Σ ==> sred Σ) (@scons s s' x).
Proof.
intros t t' Ht σ σ' Hσ. constructor. intros i. depelim i ; simpl_subst.
- assumption.
- now rewrite Hσ.
Qed.

#[export] Instance red_srcomp {Σ s s' s''} :
  Proper (sred Σ ==> eq ==> sred Σ) (@srcomp s s' s'').
Proof.
intros σ σ' Hσ ρ ρ' <-. constructor. intros i. simpl_subst.
now rewrite Hσ.
Qed.

#[export] Instance red_rscomp {Σ s s' s''} ρ :
  Proper (sred Σ ==> sred Σ) (@rscomp s s' s'' ρ).
Proof.
intros σ σ' Hσ. constructor. intros i. simpl_subst.
now rewrite Hσ.
Qed.

#[export] Instance red_sup {Σ s s' x} :
  Proper (sred Σ ==> sred Σ) (@sup s s' x).
Proof. intros σ σ' Hσ. unfold sup. now rewrite Hσ. Qed.

(** Compatibility of substitution with [red1]. Note that a single reduction in
    the substitution can cause several reductions in the result, so here we fix
    the substitution [σ]. *)
#[export] Instance red1_substitute_l {Σ s s'} (σ : subst s s') :
  Proper (red1 Σ ==> red1 Σ) (substitute σ).
Proof.
intros t t' H. induction H in s', σ |- * ; simpl_subst.
- cbn. apply red1_beta_alt. f_equal. now simpl_subst.
- eapply red1_evar_expand. eassumption.
- now apply red1_lam_l.
- now apply red1_lam_r.
- now apply red1_prod_l.
- now apply red1_prod_r.
- now apply red1_app_l.
- apply red1_app_r, OnOne2_map. revert H. apply OnOne2_consequence. firstorder.
Qed.

(** Substitution lemma for [red]. *)
#[export] Instance red_substitute {Σ s s'} :
  Proper (sred Σ ==> red Σ ==> red Σ) (@substitute s s').
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

#[export] Instance red_scomp {Σ s s' s''} :
  Proper (sred Σ ==> sred Σ ==> sred Σ) (@scomp s s' s'').
Proof.
intros σ σ' Hσ τ τ' Hτ. constructor. intros i. simpl_subst.
now rewrite Hτ, Hσ.
Qed.