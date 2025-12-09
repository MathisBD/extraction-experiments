From Metaprog Require Import Prelude Data.Term Data.Context.
From Metaprog.MetaTheory Require Import Reduction Confluence.

(** This module defines the conversion relation [conv] on [term]
    and develops the equational theory of [conv]. *)

(***********************************************************************)
(** * Conversion relation [conv]. *)
(***********************************************************************)

(** Conversion relation, defined as the smallest equivalence relation containing [red1]. *)
Inductive conv {s} : term s -> term s -> Prop :=
| conv_of_red1 t1 t2 : red1 t1 t2 -> conv t1 t2
| conv_refl t : conv t t
| conv_sym t1 t2 : conv t1 t2 -> conv t2 t1
| conv_trans t1 t2 t3 : conv t1 t2 -> conv t2 t3 -> conv t1 t3.

Derive Signature for conv.

#[export] Instance conv_Reflexive s : Reflexive (@conv s).
Proof. intros t. apply conv_refl. Qed.

#[export] Instance conv_Symmetric s : Symmetric (@conv s).
Proof. intros t1 t2. apply conv_sym. Qed.

#[export] Instance conv_Transitive s : Transitive (@conv s).
Proof. intros t. apply conv_trans. Qed.

Lemma conv_of_red {s} (t u : term s) :
  red t u -> conv t u.
Proof.
intros H. induction H.
- apply conv_of_red1. assumption.
- reflexivity.
- etransitivity ; eauto.
Qed.

(***********************************************************************)
(** * Church-Rosser theorem. *)
(***********************************************************************)

(** The Church-Rosser theorem is a direct consequence of the confluence lemma.
    We use Church-Rosser to prove inversion lemmas for [conv]. *)
Lemma church_rosser {s} (t1 t2 : term s) :
  conv t1 t2 -> exists u, red t1 u /\ red t2 u.
Proof.
intros H. depind H.
- exists t2. split ; [now apply red_of_red1 | reflexivity].
- exists t. now split.
- destruct IHconv as (u & H1 & H2). exists u. now split.
- destruct IHconv1 as (u1 & H1 & H2). destruct IHconv2 as (u2 & H3 & H4).
  destruct (red_confluence t2 u1 u2 H2 H3) as (u & H5 & H6).
  exists u. split ; etransitivity ; eassumption.
Qed.

(***********************************************************************)
(** * Congruence lemmas. *)
(***********************************************************************)

Section CongruenceLemmas.
  Context {s : scope}.

  Lemma conv_beta_congr x (ty : term s) body arg args :
    conv (TApp (TLam x ty body) (arg :: args)) (TApp (body[x := arg]) args).
  Proof. apply conv_of_red1. constructor. Qed.

  Lemma conv_lam_congr x (ty ty' : term s) body body' :
    conv ty ty' ->
    conv body body' ->
    conv (TLam x ty body) (TLam x ty' body').
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
    conv a a' ->
    conv b b' ->
    conv (TProd x a b) (TProd x a' b').
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

  Lemma conv_app_congr (f f' : term s) args args' :
    conv f f' ->
    All2 conv args args' ->
    conv (TApp f args) (TApp f' args).
  Proof.
  intros Hf Hargs. transitivity (TApp f' args).
  - clear Hargs. induction Hf.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  - clear Hf. induction Hargs.
    + reflexivity.
    + admit.
  Admitted.

End CongruenceLemmas.

(***********************************************************************)
(** * Inversion lemmas. *)
(***********************************************************************)

#[export] Instance tag_EqDec : EqDec tag.
Proof. intros [] []. now left. Qed.

Section InversionLemmas.
  Context {s : scope}.

  Lemma conv_lam_inv x (ty ty' : term s) body body' :
    conv (TLam x ty body) (TLam x ty' body') ->
    conv ty ty' /\ conv body body'.
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
    conv (TLam x a b) (TLam x a' b') ->
    conv a a' /\ conv b b'.
  Proof.
  intros H. apply church_rosser in H. destruct H as (t & H1 & H2).
  apply red_lam_inv in H1, H2.
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
