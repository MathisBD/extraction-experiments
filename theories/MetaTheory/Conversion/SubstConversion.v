From Metaprog Require Import Prelude.
From Metaprog.MetaTheory Require Export Conversion.TermConversion.

(** This module defines the conversion relation [sconv] on substitutions
    and proves basic lemmas, notably:
    - The Church-Rosser lemma for substitutions.
    - Compatibility of conversion with renaming and substitution. *)

(***********************************************************************)
(** * Conversion relation on substitutions. *)
(***********************************************************************)

(** Conversion on substitutions is just pointwise conversion.
    We wrap the definition in a record to avoid setoid rewrite issues. *)
Record sconv {s s'} (Σ : evar_map) (σ σ' : subst s s') : Prop := {
  sconv_prop : forall i, Σ ⊢ sapply σ i ≡ sapply σ' i
}.

#[export] Instance sconv_Reflexive s s' Σ : Reflexive (@sconv s s' Σ).
Proof. intros σ. constructor. reflexivity. Qed.

#[export] Instance sconv_Symmetric s s' Σ : Symmetric (@sconv s s' Σ).
Proof. intros σ σ' [Hσ]. constructor. intros i. now symmetry. Qed.

#[export] Instance sconv_Transitive s s' Σ : Transitive (@sconv s s' Σ).
Proof.
intros σ1 σ2 σ3 [H1] [H2]. constructor. intros i. etransitivity ; eauto.
Qed.

#[export] Instance conv_sapply {s s'} Σ :
  Proper (sconv Σ ==> eq ==> conv Σ) (@sapply s s').
Proof. intros σ σ' [Hσ] i ? <-. apply Hσ. Qed.

#[export] Instance sconv_of_sred {s s'} Σ :
  subrelation (@sred s s' Σ) (@sconv s s' Σ).
Proof. intros σ σ' Hσ. constructor. intros i. now rewrite Hσ. Qed.

#[export] Instance sconv_of_sred_flip {s s'} Σ :
  subrelation (Basics.flip (@sred s s' Σ)) (@sconv s s' Σ).
Proof. intros σ σ' Hσ. constructor. intros i. now rewrite Hσ. Qed.

(***********************************************************************)
(** * Church-Rosser lemma. *)
(***********************************************************************)

(** Church-Rosser lemma on substitutions.
    This is a simple consequence of the Church-Rosser lemma on terms. *)
Lemma church_rosser_subst {s s' Σ} (σ σ' : subst s s') :
  sconv Σ σ σ' ->
  exists τ, sred Σ σ τ /\ sred Σ σ' τ.
Proof.
revert s' σ σ'. induction s.
- intros s' σ σ' Hσ. exists (sren wk_idx). split ; constructor ; intros i ; depelim i.
- intros s' σ σ' Hσ.
  specialize (IHs s' (rscomp rshift σ) (rscomp rshift σ')).
  forward IHs. { constructor. intros i. simpl_subst. now rewrite Hσ. }
  destruct IHs as (τ & H1 & H2).
  assert (exists t, Σ ⊢ sapply σ I0 ~~> t /\ Σ ⊢ sapply σ' I0 ~~> t) as (t & Ht1 & Ht2).
  { apply church_rosser. now rewrite Hσ. }
  exists (scons x t τ). split.
  + constructor. intros i. depelim i ; simpl_subst.
    * exact Ht1.
    * destruct H1 as [H1]. specialize (H1 i). simpl_subst in H1. exact H1.
  + constructor. intros i. depelim i ; simpl_subst.
    * exact Ht2.
    * destruct H2 as [H2]. specialize (H2 i). simpl_subst in H2. exact H2.
Qed.

(***********************************************************************)
(** * Compatibility of conversion with renaming and substitution. *)
(***********************************************************************)

#[export] Instance conv_rename {s s' Σ} (ρ : ren s s') :
  Proper (conv Σ ==> conv Σ) (rename ρ).
Proof.
intros t t' H. apply church_rosser in H. destruct H as (u & H1 & H2).
now rewrite H1, H2.
Qed.

#[export] Instance conv_substitute {s s' Σ} :
  Proper (sconv Σ ==> conv Σ ==> conv Σ) (@substitute s s').
Proof.
intros σ σ' Hσ t t' Ht.
apply church_rosser in Ht. destruct Ht as (u & -> & ->).
apply church_rosser_subst in Hσ. destruct Hσ as (? & -> & ->).
reflexivity.
Qed.

#[export] Instance conv_scons {s s' x Σ} :
  Proper (conv Σ ==> sconv Σ ==> sconv Σ) (@scons s s' x).
Proof.
intros t t' Ht σ σ' Hσ. constructor. intros i.
apply church_rosser in Ht. destruct Ht as (? & -> & ->).
apply church_rosser_subst in Hσ. destruct Hσ as (? & -> & ->).
reflexivity.
Qed.

#[export] Instance conv_srcomp {s s' x Σ} :
  Proper (sconv Σ ==> eq ==> sconv Σ) (@srcomp s s' x).
Proof.
intros σ σ' Hσ ρ ρ' <-. constructor. intros i.
apply church_rosser_subst in Hσ. destruct Hσ as (? & -> & ->).
reflexivity.
Qed.

#[export] Instance conv_rscomp {s s' x Σ} :
  Proper (eq ==> sconv Σ ==> sconv Σ) (@rscomp s s' x).
Proof.
intros ρ ρ' <- σ σ' Hσ. constructor. intros i.
apply church_rosser_subst in Hσ. destruct Hσ as (? & -> & ->).
reflexivity.
Qed.

#[export] Instance conv_sup {s s' x Σ} :
  Proper (sconv Σ ==> sconv Σ) (@sup s s' x).
Proof.
intros σ σ' Hσ. apply church_rosser_subst in Hσ.
destruct Hσ as (? & -> & ->). reflexivity.
Qed.

#[export] Instance conv_scomp {s s' x Σ} :
  Proper (sconv Σ ==> sconv Σ ==> sconv Σ) (@scomp s s' x).
Proof.
intros σ σ' Hσ τ τ' Hτ. apply church_rosser_subst in Hσ, Hτ.
destruct Hσ as (? & -> & ->). destruct Hτ as (? & -> & ->).
reflexivity.
Qed.

