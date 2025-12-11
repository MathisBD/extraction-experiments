From Metaprog Require Import Prelude.
From Metaprog.MetaTheory Require Export Confluence.

(** This module defines the conversion relation [conv] on [term]
    and develops the equational theory of [conv]. *)

(***********************************************************************)
(** * Conversion relation [conv]. *)
(***********************************************************************)

Reserved Notation "Γ |- t ≡ u"
  (at level 50, no associativity, t at next level, u at next level).

(** Conversion relation, defined as the smallest equivalence relation containing [red1]. *)
Inductive conv {s} Σ : term s -> term s -> Prop :=
| conv_of_red1 t1 t2 : Σ |- t1 ~>₁ t2 -> Σ |- t1 ≡ t2
| conv_refl t : Σ |- t ≡ t
| conv_sym t1 t2 : Σ |- t1 ≡ t2 -> Σ |- t2 ≡ t1
| conv_trans t1 t2 t3 : Σ |- t1 ≡ t2 -> Σ |- t2 ≡ t3 -> Σ |- t1 ≡ t3

where "Σ |- t ≡ u" := (conv Σ t u).

Derive Signature for conv.

#[export] Instance conv_Reflexive s Σ : Reflexive (@conv s Σ).
Proof. intros t. apply conv_refl. Qed.

#[export] Instance conv_Symmetric s Σ : Symmetric (@conv s Σ).
Proof. intros t1 t2. apply conv_sym. Qed.

#[export] Instance conv_Transitive s Σ : Transitive (@conv s Σ).
Proof. intros t. apply conv_trans. Qed.

Lemma conv_of_red {s} Σ (t u : term s) :
  Σ |- t ~> u -> Σ |- t ≡ u.
Proof.
intros H. induction H.
- reflexivity.
- rewrite IHrefl_trans_clos. now apply conv_of_red1.
Qed.

(***********************************************************************)
(** * Church-Rosser theorem. *)
(***********************************************************************)

(** The Church-Rosser theorem is a direct consequence of the confluence lemma.
    We use Church-Rosser to prove inversion lemmas for [conv]. *)
Lemma church_rosser {s} Σ (t1 t2 : term s) :
  Σ |- t1 ≡ t2 ->
  exists u, Σ |- t1 ~> u /\ Σ |- t2 ~> u.
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
    Σ |- TApp (TLam x ty body) (arg :: args) ≡ TApp (body[x := arg]) args.
  Proof. apply conv_of_red1. constructor. Qed.

  Lemma conv_lam_congr x (ty ty' : term s) body body' :
    Σ |- ty ≡ ty' ->
    Σ |- body ≡ body' ->
    Σ |- TLam x ty body ≡ TLam x ty' body'.
  Proof.
  intros Hty Hbody. transitivity (TLam x ty' body).
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

  Lemma conv_prod_congr x (a a' : term s) b b' :
    Σ |- a ≡ a' ->
    Σ |- b ≡ b' ->
    Σ |- TProd x a b ≡ TProd x a' b'.
  Proof.
  intros Ha Hb. transitivity (TProd x a' b).
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
    Σ |- TApp f (l ++ args) ≡ TApp f (l ++ args').
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

  Lemma conv_app_congr (f f' : term s) args args' :
    Σ |- f ≡ f' ->
    All2 (conv Σ) args args' ->
    Σ |- TApp f args ≡ TApp f' args'.
  Proof.
  intros Hf Hargs. transitivity (TApp f' args).
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

  Lemma conv_lam_inv x (ty ty' : term s) body body' :
    Σ |- TLam x ty body ≡ TLam x ty' body' ->
    Σ |- ty ≡ ty' /\ Σ |- body ≡ body'.
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

  Lemma conv_prod_inv x (a a' : term s) b b' :
    Σ |- TProd x a b ≡ TProd x a' b' ->
    Σ |- a ≡ a' /\ Σ |- b ≡ b'.
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
