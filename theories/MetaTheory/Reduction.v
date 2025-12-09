From Metaprog Require Import Prelude Data.Term Data.Context.

(** This module defines:
    - The one-step strong reduction relation [red1] on [term].
    - The reduction relation [red] on [term] and its basic properties. *)

(***********************************************************************)
(** * One-step reduction relation [red1]. *)
(***********************************************************************)

Unset Elimination Schemes.

(** Strong one-step reduction relation. This relation is _not_ deterministic. *)
Inductive red1 {s} : term s -> term s -> Prop :=

(** Beta-reduction rule. *)
| red1_beta x ty body arg args :
    red1 (TApp (TLam x ty body) (arg :: args)) (TApp (body[x := arg]) args)

(** Congrence rules for [TLam]. *)
| red1_lam_l x ty ty' body :
    red1 ty ty' -> red1 (TLam x ty body) (TLam x ty' body)
| red1_lam_r x ty body body' :
    red1 body body' -> red1 (TLam x ty body) (TLam x ty body')

(** Congruence rules for [TProd]. *)
| red1_prod_l x a a' b :
    red1 a a' -> red1 (TProd x a b) (TProd x a' b)
| red1_prod_r x a b b' :
    red1 b b' -> red1 (TProd x a b) (TProd x a b')

(** Congruence rules for [TApp]. *)
| red1_app_l f f' args :
    red1 f f' -> red1 (TApp f args) (TApp f' args)
| red1_app_r f args args' :
    OnOne2 red1 args args' -> red1 (TApp f args) (TApp f args').

Set Elimination Schemes.

Derive Signature for red1.

(** Induction principle for [red1]. We can't use Rocq's default induction principle
    because [red1] is nested over [OnOne2]. *)
Lemma red1_ind (P : forall s, term s -> term s -> Prop) :
  (forall s x ty body arg args,
    P s (TApp (TLam x ty body) (arg :: args)) (TApp (body[x := arg]) args)) ->
  (forall s x ty ty' body,
    red1 ty ty' ->
    P s ty ty' ->
    P s (TLam x ty body) (TLam x ty' body)) ->
  (forall s x ty body body',
    red1 body body' ->
    P (s ▷ x) body body' ->
    P s (TLam x ty body) (TLam x ty body')) ->
  (forall s x a a' b,
    red1 a a' ->
    P s a a' ->
    P s (TProd x a b) (TProd x a' b)) ->
  (forall s x a b b',
    red1 b b' ->
    P (s ▷ x) b b' ->
    P s (TProd x a b) (TProd x a b')) ->
  (forall s f f' args,
    red1 f f' ->
    P s f f' ->
    P s (TApp f args) (TApp f' args)) ->
  (forall s f args args',
    OnOne2 (fun arg arg' => red1 arg arg' /\ P s arg arg') args args' ->
    P s (TApp f args) (TApp f args')) ->
  forall s t t', red1 t t' -> P s t t'.
Proof.
intros Hbeta Hlam_l Hlam_r Hprod_l Hprod_r Happ_l Happ_r. fix IH 4.
intros s t t' Hred. destruct Hred.
- apply Hbeta.
- apply Hlam_l ; auto.
- apply Hlam_r ; auto.
- apply Hprod_l ; auto.
- apply Hprod_r ; auto.
- apply Happ_l ; auto.
- apply Happ_r. revert args args' H. fix IHargs 3. intros args args' H. destruct H.
  + constructor. split ; auto.
  + constructor. now apply IHargs.
Qed.

(***********************************************************************)
(** * Reduction relation [red]. *)
(***********************************************************************)

(** Strong reduction relation, defined as the reflexive-transitive closure of [red1]. *)
Inductive red {s} : term s -> term s -> Prop :=
| red_of_red1 t1 t2 : red1 t1 t2 -> red t1 t2
| red_refl t : red t t
| red_trans t1 t2 t3 : red t1 t2 -> red t2 t3 -> red t1 t3.

Derive Signature for red.

#[export] Instance red_Reflexive s : Reflexive (@red s).
Proof. intros t. apply red_refl. Qed.

#[export] Instance red_Transitive s : Transitive (@red s).
Proof. intros t1 t2 t3. apply red_trans. Qed.

(***********************************************************************)
(** * Congruence lemmas. *)
(***********************************************************************)

Section CongruenceLemmas.
  Context {s : scope}.

  Lemma red_beta x (ty : term s) body arg args :
    red (TApp (TLam x ty body) (arg :: args)) (TApp (body[x := arg]) args).
  Proof. apply red_of_red1. constructor. Qed.

  Lemma red_lam_congr x (ty ty' : term s) body body' :
    red ty ty' ->
    red body body' ->
    red (TLam x ty body) (TLam x ty' body').
  Proof.
  intros Hty Hbody. transitivity (TLam x ty body').
  - clear Hty. induction Hbody.
    + apply red_of_red1. now constructor.
    + reflexivity.
    + etransitivity ; eauto.
  - clear Hbody. induction Hty.
    + apply red_of_red1. now constructor.
    + reflexivity.
    + etransitivity ; eauto.
  Qed.

  Lemma red_prod_congr x (a a' : term s) b b' :
    red a a' ->
    red b b' ->
    red (TProd x a b) (TProd x a' b').
  Proof.
  intros Ha Hb. transitivity (TProd x a b').
  - clear Ha. induction Hb.
    + apply red_of_red1. now constructor.
    + reflexivity.
    + etransitivity ; eauto.
  - clear Hb. induction Ha.
    + apply red_of_red1. now constructor.
    + reflexivity.
    + etransitivity ; eauto.
  Qed.

  Lemma red_app_congr_aux (f : term s) l (args args' : list (term s)) :
    All2 red args args' ->
    red (TApp f (l ++ args)) (TApp f (l ++ args')).
  Proof.
  intros H. revert f l. depind H ; intros f l.
  - reflexivity.
  - transitivity (TApp f (l ++ y :: xs)).
    + clear IHAll2 H0. induction H.
      * apply red_of_red1, red1_app_r. apply OnOne2_app_r, OnOne2_head. assumption.
      * reflexivity.
      * etransitivity ; eauto.
    + specialize (IHAll2 f (l ++ [y])). rewrite <-!app_assoc in IHAll2.
      cbn in IHAll2. exact IHAll2.
  Qed.

  Lemma red_app_congr (f f' : term s) args args' :
    red f f' ->
    All2 red args args' ->
    red (TApp f args) (TApp f' args').
  Proof.
  intros Hf Hargs. transitivity (TApp f' args).
  - clear Hargs. induction Hf.
    + apply red_of_red1. now constructor.
    + reflexivity.
    + etransitivity ; eauto.
  - clear f Hf. apply red_app_congr_aux with (l := []). assumption.
  Qed.

End CongruenceLemmas.

(***********************************************************************)
(** * Inversion lemmas. *)
(***********************************************************************)

Section InversionLemmas.
  Context {s : scope}.

  Lemma red_type_inv (t : term s) :
    red TType t -> t = TType.
  Proof.
  intros H. depind H.
  - depelim H.
  - reflexivity.
  - subst. specialize (IHred2 t3 eq_refl). now subst.
  Qed.

  Lemma red_var_inv (i : index s) (t : term s) :
    red (TVar i) t -> t = TVar i.
  Proof.
  intros H. depind H.
  - depelim H.
  - reflexivity.
  - subst. specialize (IHred2 i t3 eq_refl). now subst.
  Qed.

  Lemma red_lam_inv x (ty : term s) body t :
    red (TLam x ty body) t ->
    exists ty' body',
      t = TLam x ty' body' /\
      red ty ty' /\
      red body body'.
  Proof.
  intros Hred. depind Hred.
  - depelim H.
    + exists ty', body. split3 ; [reflexivity | now apply red_of_red1 | reflexivity].
    + exists ty, body'. split3 ; [reflexivity | reflexivity | now apply red_of_red1].
  - exists ty, body. now split3.
  - destruct IHHred1 as (ty' & body' & -> & Hty1 & Hbody1).
    specialize (IHHred2 x ty' body' t3 eq_refl).
    destruct IHHred2 as (ty'' & body'' & -> & Hty2 & Hbody2).
    exists ty'', body''. split3 ; [reflexivity | etransitivity ; eauto ..].
  Qed.

  Lemma red_prod_inv x (a : term s) b t :
    red (TProd x a b) t ->
    exists a' b',
      t = TProd x a' b' /\
      red a a' /\
      red b b'.
  Proof.
  intros Hred. depind Hred.
  - depelim H.
    + exists a', b. split3 ; [reflexivity | now apply red_of_red1 | reflexivity].
    + exists a, b'. split3 ; [reflexivity | reflexivity | now apply red_of_red1].
  - exists a, b. now split3.
  - destruct IHHred1 as (a' & b' & -> & Ha1 & Hb1).
    specialize (IHHred2 x a' b' t3 eq_refl).
    destruct IHHred2 as (a'' & b'' & -> & Ha2 & Hb2).
    exists a'', b''. split3 ; [reflexivity | etransitivity ; eauto ..].
  Qed.

  Lemma red_evar_inv ev (t : term s) :
    red (TEvar ev) t -> t = TEvar ev.
  Proof.
  intros H. depind H.
  - depelim H.
  - reflexivity.
  - subst. specialize (IHred2 ev t3 eq_refl). now subst.
  Qed.

End InversionLemmas.