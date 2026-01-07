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
Record sconv (flags : red_flags) (Σ : evar_map) {s s'} (σ σ' : subst s s') : Prop := {
  sconv_prop : forall i, Σ ⊢ sapply σ i ≡{flags} sapply σ' i
}.

#[export] Instance conv_sapply flags Σ s s' :
  Proper (sconv flags Σ ==> eq ==> conv flags Σ) (@sapply s s').
Proof. intros σ σ' [Hσ] i ? <-. apply Hσ. Qed.

(***********************************************************************)
(** * Typeclass instances for setoid rewriting. *)
(***********************************************************************)

Section Instances.
  Context {flags : red_flags} {Σ : evar_map} {s s' : scope}.

  #[export] Instance sconv_Reflexive : Reflexive (@sconv flags Σ s s').
  Proof. intros σ. constructor. reflexivity. Qed.

  #[export] Instance sconv_Symmetric : Symmetric (@sconv flags Σ s s').
  Proof. intros σ σ' [Hσ]. constructor. intros i. now symmetry. Qed.

  #[export] Instance sconv_Transitive : Transitive (@sconv flags Σ s s').
  Proof.
  intros σ1 σ2 σ3 [H1] [H2]. constructor. intros i. etransitivity ; eauto.
  Qed.

  #[export] Instance sconv_of_sred :
    subrelation (@sred flags Σ s s') (@sconv flags Σ s s').
  Proof. intros σ σ' Hσ. constructor. intros i. now rewrite Hσ. Qed.

  #[export] Instance sconv_of_sred_flip :
    subrelation (Basics.flip (@sred flags Σ s s')) (@sconv flags Σ s s').
  Proof. intros σ σ' Hσ. constructor. intros i. now rewrite Hσ. Qed.

End Instances.

Lemma sconv_extend_flags {flags1 flags2 Σ s s'} :
  red_flags_incl flags1 flags2 ->
  subrelation (@sconv flags1 Σ s s') (@sconv flags2 Σ s s').
Proof.
intros Hf σ1 σ2 Hσ. constructor. intros i. apply (conv_extend_flags Hf).
apply Hσ.
Qed.

Lemma sconv_extend_evm {flags Σ1 Σ2 s s'} :
  Σ1 ⊑ Σ2 ->
  subrelation (@sconv flags Σ1 s s') (@sconv flags Σ2 s s').
Proof.
intros HΣ σ1 σ2 Hσ. constructor. intros i. apply (conv_extend_evm HΣ).
apply Hσ.
Qed.

(***********************************************************************)
(** * Church-Rosser lemma. *)
(***********************************************************************)

(** Church-Rosser lemma on substitutions.
    This is a simple consequence of the Church-Rosser lemma on terms. *)
Lemma church_rosser_subst {flags Σ s s'} (σ σ' : subst s s') :
  sconv flags Σ σ σ' ->
  exists τ, sred flags Σ σ τ /\ sred flags Σ σ' τ.
Proof.
revert s' σ σ'. induction s.
- intros s' σ σ' Hσ. exists (sren wk_idx). split ; constructor ; intros i ; depelim i.
- intros s' σ σ' Hσ.
  specialize (IHs s' (rscomp rshift σ) (rscomp rshift σ')).
  forward IHs. { constructor. intros i. simpl_subst. now rewrite Hσ. }
  destruct IHs as (τ & H1 & H2).
  assert (exists t, Σ ⊢ sapply σ I0 ~~>{flags} t /\ Σ ⊢ sapply σ' I0 ~~>{flags} t) as (t & Ht1 & Ht2).
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

Section Substitutivity.
  Context {flags : red_flags} {Σ : evar_map} {s s' s'' : scope} {x : tag}.

  #[export] Instance conv_rename (ρ : ren s s') :
    Proper (conv flags Σ ==> conv flags Σ) (rename ρ).
  Proof.
  intros t t' H. apply church_rosser in H. destruct H as (u & H1 & H2).
  now rewrite H1, H2.
  Qed.

  #[export] Instance conv_substitute :
    Proper (sconv flags Σ ==> conv flags Σ ==> conv flags Σ) (@substitute s s').
  Proof.
  intros σ σ' Hσ t t' Ht.
  apply church_rosser in Ht. destruct Ht as (u & -> & ->).
  apply church_rosser_subst in Hσ. destruct Hσ as (? & -> & ->).
  reflexivity.
  Qed.

  #[export] Instance conv_scons :
    Proper (conv flags Σ ==> sconv flags Σ ==> sconv flags Σ) (@scons s s' x).
  Proof.
  intros t t' Ht σ σ' Hσ. constructor. intros i.
  apply church_rosser in Ht. destruct Ht as (? & -> & ->).
  apply church_rosser_subst in Hσ. destruct Hσ as (? & -> & ->).
  reflexivity.
  Qed.

  #[export] Instance conv_srcomp :
    Proper (sconv flags Σ ==> eq ==> sconv flags Σ) (@srcomp s s' s'').
  Proof.
  intros σ σ' Hσ ρ ρ' <-. constructor. intros i.
  apply church_rosser_subst in Hσ. destruct Hσ as (? & -> & ->).
  reflexivity.
  Qed.

  #[export] Instance conv_rscomp :
    Proper (eq ==> sconv flags Σ ==> sconv flags Σ) (@rscomp s s' s'').
  Proof.
  intros ρ ρ' <- σ σ' Hσ. constructor. intros i.
  apply church_rosser_subst in Hσ. destruct Hσ as (? & -> & ->).
  reflexivity.
  Qed.

  #[export] Instance conv_sup :
    Proper (sconv flags Σ ==> sconv flags Σ) (@sup s s' x).
  Proof.
  intros σ σ' Hσ. apply church_rosser_subst in Hσ.
  destruct Hσ as (? & -> & ->). reflexivity.
  Qed.

  #[export] Instance conv_scomp :
    Proper (sconv flags Σ ==> sconv flags Σ ==> sconv flags Σ) (@scomp s s' s'').
  Proof.
  intros σ σ' Hσ τ τ' Hτ. apply church_rosser_subst in Hσ, Hτ.
  destruct Hσ as (? & -> & ->). destruct Hτ as (? & -> & ->).
  reflexivity.
  Qed.

End Substitutivity.
