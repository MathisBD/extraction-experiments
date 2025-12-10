From Metaprog Require Import Prelude.
From Metaprog.MetaTheory Require Export Relations Substitution.

(** This module defines:
    - The one-step strong reduction relation [red1] on [term].
    - The strong reduction relation [red] on [term] and its basic properties. *)

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
Definition red {s} : term s -> term s -> Prop :=
  refl_trans_clos (@red1 s).

Arguments red : simpl never.

Lemma red_same {s} (t u : term s) :
  t = u -> red t u.
Proof. intros ->. reflexivity. Qed.

Lemma red_of_red1 {s} (t u : term s) :
  red1 t u -> red t u.
Proof. apply refl_trans_clos_one. Qed.

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
    + reflexivity.
    + rewrite IHHbody. now apply red_of_red1, red1_lam_r.
  - clear Hbody. induction Hty.
    + reflexivity.
    + rewrite IHHty. now apply red_of_red1, red1_lam_l.
  Qed.

  Lemma red_prod_congr x (a a' : term s) b b' :
    red a a' ->
    red b b' ->
    red (TProd x a b) (TProd x a' b').
  Proof.
  intros Ha Hb. transitivity (TProd x a b').
  - clear Ha. induction Hb.
    + reflexivity.
    + rewrite IHHb. now apply red_of_red1, red1_prod_r.
  - clear Hb. induction Ha.
    + reflexivity.
    + rewrite IHHa. now apply red_of_red1, red1_prod_l.
  Qed.

  Lemma red_app_congr_aux (f : term s) l (args args' : list (term s)) :
    All2 red args args' ->
    red (TApp f (l ++ args)) (TApp f (l ++ args')).
  Proof.
  intros H. revert f l. depind H ; intros f l.
  - reflexivity.
  - transitivity (TApp f (l ++ y :: xs)).
    + clear IHAll2 H0. induction H.
      * reflexivity.
      * rewrite IHrefl_trans_clos. apply red_of_red1, red1_app_r.
        now apply OnOne2_app_r, OnOne2_head.
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
    + reflexivity.
    + rewrite IHHf. now apply red_of_red1, red1_app_l.
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
  - reflexivity.
  - subst. depelim H0.
  Qed.

  Lemma red_var_inv (i : index s) (t : term s) :
    red (TVar i) t -> t = TVar i.
  Proof.
  intros H. depind H.
  - reflexivity.
  - subst. depelim H0.
  Qed.

  Lemma red_lam_inv x (ty : term s) body t :
    red (TLam x ty body) t ->
    exists ty' body',
      t = TLam x ty' body' /\
      red ty ty' /\
      red body body'.
  Proof.
  intros Hred. depind Hred.
  - exists ty, body. now split3.
  - destruct IHHred as (ty' & body' & -> & Hty1 & Hbody1). depelim H.
    + exists ty'0, body'. split3 ; [reflexivity | | assumption].
      rewrite Hty1. now apply red_of_red1.
    + exists ty', body'0. split3 ; [reflexivity | assumption |].
      rewrite Hbody1. now apply red_of_red1.
  Qed.

  Lemma red_prod_inv x (a : term s) b t :
    red (TProd x a b) t ->
    exists a' b',
      t = TProd x a' b' /\
      red a a' /\
      red b b'.
  Proof.
  intros Hred. depind Hred.
  - exists a, b. now split3.
  - destruct IHHred as (a' & b' & -> & Ha1 & Hb1). depelim H.
    + exists a'0, b'. split3 ; [reflexivity | | assumption].
      rewrite Ha1. now apply red_of_red1.
    + exists a', b'0. split3 ; [reflexivity | assumption |].
      rewrite Hb1. now apply red_of_red1.
  Qed.

  Lemma red_evar_inv ev (t : term s) :
    red (TEvar ev) t -> t = TEvar ev.
  Proof.
  intros H. depind H.
  - reflexivity.
  - subst. depelim H0.
  Qed.

End InversionLemmas.

(***********************************************************************)
(** * Compatibility with renaming and substitution. *)
(***********************************************************************)

Section SubstitutionLemma.
  Context {s s' : scope}.

  (** Renaming lemma for [red1]. *)
  Lemma red1_rename (t t' : term s) (ρ : ren s s') :
    red1 t t' -> red1 (rename ρ t) (rename ρ t').
  Proof.
  intros H. induction H in s', ρ |- * ; simpl_subst.
  - cbn.
    assert (substitute (srcomp (scons x arg sid) ρ) body =
            substitute (scons x (rename ρ arg) sid) (rename (rup x ρ) body)) as ->.
    { simpl_subst. f_equal. subst_ext i. depelim i ; simpl_subst ; reflexivity. }
    apply red1_beta.
  - now apply red1_lam_l.
  - now apply red1_lam_r.
  - now apply red1_prod_l.
  - now apply red1_prod_r.
  - now apply red1_app_l.
  - apply red1_app_r, OnOne2_map. revert H. apply OnOne2_consequence. firstorder.
  Qed.

  (** Renaming lemma for [red]. *)
  Lemma red_rename (t t' : term s) (ρ : ren s s') :
    red t t' -> red (rename ρ t) (rename ρ t').
  Proof.
  intros H. induction H.
  - reflexivity.
  - rewrite IHrefl_trans_clos. now apply red_of_red1, red1_rename.
  Qed.

  (** Substitution lemma for [red1]. *)
  Lemma red1_substitute (t t' : term s) (σ : subst s s') :
    red1 t t' -> red1 (substitute σ t) (substitute σ t').
  Proof.
  intros H. induction H in s', σ |- * ; simpl_subst.
  - cbn.
    assert (substitute (scomp (scons x arg sid) σ) body =
            substitute (scons x (substitute σ arg) sid) (substitute (sup x σ) body)) as ->.
    { simpl_subst. f_equal. subst_ext i. depelim i ; simpl_subst ; reflexivity. }
    apply red1_beta.
  - now apply red1_lam_l.
  - now apply red1_lam_r.
  - now apply red1_prod_l.
  - now apply red1_prod_r.
  - now apply red1_app_l.
  - apply red1_app_r, OnOne2_map. revert H. apply OnOne2_consequence. firstorder.
  Qed.

  (** Substitution lemma for [red]. *)
  Lemma red_substitute (t t' : term s) (σ : subst s s') :
    red t t' -> red (substitute σ t) (substitute σ t').
  Proof.
  intros H. induction H.
  - reflexivity.
  - rewrite IHrefl_trans_clos. now apply red_of_red1, red1_substitute.
  Qed.

End SubstitutionLemma.