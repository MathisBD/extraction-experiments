From Metaprog Require Import Prelude.
From Metaprog.MetaTheory Require Export Confluence.

(** This module defines the conversion relation [conv] on [term]
    and develops the equational theory of [conv]. *)

(***********************************************************************)
(** * Conversion relation on terms. *)
(***********************************************************************)

Reserved Notation "Γ ⊢ t ≡ u"
  (at level 50, no associativity, t at next level, u at next level).

(** Conversion relation, defined as the smallest equivalence relation containing [red1]. *)
Inductive conv {s} Σ : term s -> term s -> Prop :=
| conv_of_red1 t1 t2 : Σ ⊢ t1 ~> t2 -> Σ ⊢ t1 ≡ t2
| conv_refl t : Σ ⊢ t ≡ t
| conv_sym t1 t2 : Σ ⊢ t1 ≡ t2 -> Σ ⊢ t2 ≡ t1
| conv_trans t1 t2 t3 : Σ ⊢ t1 ≡ t2 -> Σ ⊢ t2 ≡ t3 -> Σ ⊢ t1 ≡ t3

where "Σ ⊢ t ≡ u" := (conv Σ t u).

Derive Signature for conv.

#[export] Instance conv_Reflexive s Σ : Reflexive (@conv s Σ).
Proof. intros t. apply conv_refl. Qed.

#[export] Instance conv_Symmetric s Σ : Symmetric (@conv s Σ).
Proof. intros t1 t2. apply conv_sym. Qed.

#[export] Instance conv_Transitive s Σ : Transitive (@conv s Σ).
Proof. intros t. apply conv_trans. Qed.

Lemma conv_of_red {s} Σ (t u : term s) :
  Σ ⊢ t ~~> u -> Σ ⊢ t ≡ u.
Proof.
intros H. induction H.
- reflexivity.
- rewrite IHred. now apply conv_of_red1.
Qed.

#[export] Instance subrelation_red_conv s Σ :
  subrelation (@red s Σ) (@conv s Σ).
Proof. intros t u H. now apply conv_of_red. Qed.

#[export] Instance subrelation_red_conv_flip s Σ :
  subrelation (@red s Σ) (Basics.flip (@conv s Σ)).
Proof. intros t u H. unfold Basics.flip. symmetry. now apply conv_of_red. Qed.

(***********************************************************************)
(** * Church-Rosser theorem. *)
(***********************************************************************)

(** The Church-Rosser theorem is a direct consequence of the confluence lemma.
    We use Church-Rosser to prove inversion lemmas for [conv]. *)
Lemma church_rosser {s} Σ (t1 t2 : term s) :
  Σ ⊢ t1 ≡ t2 ->
  exists u, Σ ⊢ t1 ~~> u /\ Σ ⊢ t2 ~~> u.
Proof.
intros H. depind H.
- exists t2. split ; [now apply red_of_red1 | reflexivity].
- exists t. now split.
- destruct IHconv as (u & H1 & H2). exists u. now split.
- destruct IHconv1 as (u1 & H1 & H2). destruct IHconv2 as (u2 & H3 & H4).
  destruct (red_confluence Σ t2 u1 u2 H2 H3) as (u & H5 & H6).
  exists u. split ; etransitivity ; eassumption.
Qed.

(***********************************************************************)
(** * Congruence lemmas. *)
(***********************************************************************)

Section CongruenceLemmas.
  Context {s : scope} (Σ : evar_map).

  Lemma conv_beta x (ty : term s) body arg args :
    Σ ⊢ TApp (TLam x ty body) (arg :: args) ≡ TApp (body[x := arg]) args.
  Proof. now rewrite red_beta. Qed.

  #[export] Instance conv_lam_congr x :
    Proper (conv Σ ==> conv Σ ==> conv Σ) (@TLam s x).
  Proof.
  intros ty ty' Hty body body' Hbody. transitivity (TLam x ty' body).
  - clear Hbody. induction Hty.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  - clear Hty. induction Hbody.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  Qed.

  #[export] Instance conv_prod_congr x :
    Proper (conv Σ ==> conv Σ ==> conv Σ) (@TProd s x).
  Proof.
  intros a a' Ha b b' Hb. transitivity (TProd x a' b).
  - clear Hb. induction Ha.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  - clear Ha. induction Hb.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  Qed.

  Lemma conv_app_congr_aux (f : term s) l (args args' : list (term s)) :
    All2 (conv Σ) args args' ->
    Σ ⊢ TApp f (l ++ args) ≡ TApp f (l ++ args').
  Proof.
  intros H. revert f l. depind H ; intros f l.
  - reflexivity.
  - transitivity (TApp f (l ++ y :: xs)).
    + clear IHAll2 H0. induction H.
      * apply conv_of_red1, red1_app_r. apply OnOne2_app_r, OnOne2_head. assumption.
      * reflexivity.
      * now symmetry.
      * etransitivity ; eauto.
    + specialize (IHAll2 f (l ++ [y])). rewrite <-!app_assoc in IHAll2.
      cbn in IHAll2. exact IHAll2.
  Qed.

  #[export] Instance conv_app_congr :
    Proper (conv Σ ==> All2 (conv Σ) ==> conv Σ) (@TApp s).
  Proof.
  intros f f' Hf args arg' Hargs. transitivity (TApp f' args).
  - clear Hargs. induction Hf.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  - apply conv_app_congr_aux with (l := []). assumption.
  Qed.

End CongruenceLemmas.

(***********************************************************************)
(** * Inversion lemmas (aka injectivity of construtors). *)
(***********************************************************************)

Section InversionLemmas.
  Context {s : scope} (Σ : evar_map).

  (** Injectivity of [TLam]. *)
  Lemma conv_lam_inv x (ty ty' : term s) body body' :
    Σ ⊢ TLam x ty body ≡ TLam x ty' body' ->
    Σ ⊢ ty ≡ ty' /\ Σ ⊢ body ≡ body'.
  Proof.
  intros H. apply church_rosser in H. destruct H as (t & H1 & H2).
  apply red_lam_inv in H1, H2.
  destruct H1 as (ty1' & body1' & -> & Hty1 & Hbody1).
  destruct H2 as (ty2' & body2' & Heq & Hty2 & Hbody2).
  depelim Heq. apply inj_right_sigma in H. depelim H. split.
  - transitivity ty1'.
    + apply conv_of_red, Hty1.
    + symmetry. apply conv_of_red, Hty2.
  - transitivity body1'.
    + apply conv_of_red, Hbody1.
    + symmetry. apply conv_of_red, Hbody2.
  Qed.

  (** Injectivity of [TProd]. *)
  Lemma conv_prod_inv x (a a' : term s) b b' :
    Σ ⊢ TProd x a b ≡ TProd x a' b' ->
    Σ ⊢ a ≡ a' /\ Σ ⊢ b ≡ b'.
  Proof.
  intros H. apply church_rosser in H. destruct H as (t & H1 & H2).
  apply red_prod_inv in H1, H2.
  destruct H1 as (a1' & b1' & -> & Ha1 & Hb1).
  destruct H2 as (a2' & b2' & Heq & Ha2 & Hb2).
  depelim Heq. apply inj_right_sigma in H. depelim H. split.
  - transitivity a1'.
    + apply conv_of_red, Ha1.
    + symmetry. apply conv_of_red, Ha2.
  - transitivity b1'.
    + apply conv_of_red, Hb1.
    + symmetry. apply conv_of_red, Hb2.
  Qed.

End InversionLemmas.

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

(** Church Rosser lemma on substitutions.
    This is a simple consequence of the Church Rosser lemma on terms. *)
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
(** * Compatibility of conversion with substitution. *)
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

