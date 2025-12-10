From Metaprog Require Import Prelude.
From Metaprog.MetaTheory Require Export Reduction.

(** This module proves the confluence lemma for the reduction relation [red]
    using the standard parallel reduction technique. *)

(***********************************************************************)
(** * Parallel reduction. *)
(***********************************************************************)

Unset Elimination Schemes.

(** Parallel reduction relation. *)
Inductive pred1 {s} : term s -> term s -> Prop :=

(** Beta-reduction rule. *)
| pred1_app_beta x ty ty' body body' arg arg' args args' :
    pred1 ty ty' ->
    pred1 body body' ->
    pred1 arg arg' ->
    All2 pred1 args args' ->
    pred1 (TApp (TLam x ty body) (arg :: args)) (TApp (body'[x := arg']) args')

(** Congrence rules. *)

| pred1_type :
    pred1 TType TType

| pred1_var i :
    pred1 (TVar i) (TVar i)

| pred1_lam x ty ty' body body' :
    pred1 ty ty' -> pred1 body body' -> pred1 (TLam x ty body) (TLam x ty' body')

| pred1_prod x a a' b b' :
    pred1 a a' -> pred1 b b' -> pred1 (TProd x a b) (TProd x a' b')

| pred1_app f f' args args' :
    pred1 f f' -> All2 pred1 args args' -> pred1 (TApp f args) (TApp f' args')

| pred1_evar ev :
    pred1 (TEvar ev) (TEvar ev).

Set Elimination Schemes.

Derive Signature for pred1.

(** Induction principle for [pred1]. We can't use Rocq's default induction principle
    because [pred1] is nested over [All2]. *)
Lemma pred1_ind (P : forall s, term s -> term s -> Prop)
  (Hbeta : forall s x ty ty' body body' arg arg' args args',
    pred1 ty ty' -> P s ty ty' ->
    pred1 body body' -> P (s ▷ x) body body' ->
    pred1 arg arg' -> P s arg arg' ->
    All2 pred1 args args' -> All2 (P s) args args' ->
    P s (TApp (TLam x ty body) (arg :: args)) (TApp (body'[x := arg']) args'))
  (Htype : forall s, P s TType TType)
  (Hvar : forall s i, P s (TVar i) (TVar i))
  (Hlam : forall s x ty ty' body body',
    pred1 ty ty' -> P s ty ty' ->
    pred1 body body' -> P (s ▷ x) body body' ->
    P s (TLam x ty body) (TLam x ty' body'))
  (Hprod : forall s x a a' b b',
    pred1 a a' -> P s a a' ->
    pred1 b b' -> P (s ▷ x) b b' ->
    P s (TProd x a b) (TProd x a' b'))
  (Happ : forall s f f' args args',
    pred1 f f' -> P s f f' ->
    All2 pred1 args args' -> All2 (P s) args args' ->
    P s (TApp f args) (TApp f' args'))
  (Hevar : forall s ev, P s (TEvar ev) (TEvar ev)) :
  forall s t t', pred1 t t' -> P s t t'.
Proof.
fix IH 4. intros s t t' Hred. destruct Hred.
- apply Hbeta with ty' ; try assumption ; try now apply IH.
  revert args args' H. fix IHargs 3. intros args args' H. destruct H.
  + constructor.
  + constructor ; auto.
- apply Htype.
- apply Hvar.
- apply Hlam ; auto.
- apply Hprod ; auto.
- apply Happ ; auto. revert args args' H. fix IHargs 3. intros args args' H. destruct H.
  + constructor.
  + constructor ; auto.
- apply Hevar.
Qed.

#[export] Instance pred1_Reflexive s : Reflexive (@pred1 s).
Proof.
intros t. induction t using term_ind' ; constructor ; try assumption.
induction args ; constructor ; depelim H ; auto.
Qed.

Lemma pred1_beta {s} x (ty : term s) body arg args :
  pred1 (TApp (TLam x ty body) (arg :: args)) (TApp (body[x := arg]) args).
Proof.
eapply pred1_app_beta.
- reflexivity.
- reflexivity.
- reflexivity.
- now apply All2_same.
Qed.

(***********************************************************************)
(** * Relating parallel reduction and standard reduction. *)
(***********************************************************************)

(** One-step reduction is included in parallel reduction. *)
Lemma pred1_of_red1 {s} (t u : term s) :
  red1 t u -> pred1 t u.
Proof.
intros H. induction H.
- apply pred1_beta.
- now apply pred1_lam.
- now apply pred1_lam.
- now apply pred1_prod.
- now apply pred1_prod.
- apply pred1_app ; [assumption|]. now apply All2_same.
- apply pred1_app ; [reflexivity|]. apply All2_of_OnOne2 ; [typeclasses eauto|].
  revert H. apply OnOne2_consequence. easy.
Qed.

(** Parallel reduction is included in standard reduction. *)
Lemma red_of_pred1 {s} (t u : term s) :
  pred1 t u -> red t u.
Proof.
intros H. induction H.
- rewrite <-red_beta.
  apply red_app_congr ; [apply red_lam_congr | constructor] ; eassumption.
- reflexivity.
- reflexivity.
- now apply red_lam_congr.
- now apply red_prod_congr.
- now apply red_app_congr.
- reflexivity.
Qed.

(** The reflexive closure of [pred1] is equal to [red]. *)
Lemma red_is_pred {s} (t u : term s) :
  red t u <-> refl_trans_clos pred1 t u.
Proof.
split ; revert t u ; apply refl_trans_clos_incl.
- intros t u H. apply refl_trans_clos_one. now apply pred1_of_red1.
- intros t u H. now apply red_of_pred1.
Qed.

(***********************************************************************)
(** * Compatibility with renaming and substitution. *)
(***********************************************************************)

(** Renaming lemma for [pred1]. *)
Lemma pred1_rename {s s'} (t t' : term s) (ρ : ren s s') :
  pred1 t t' -> pred1 (rename ρ t) (rename ρ t').
Proof.
intros H. induction H in s', ρ |- * ; simpl_subst.
- cbn.
  assert (substitute (srcomp (scons x arg' sid) ρ) body' =
          substitute (scons x (rename ρ arg') sid) (rename (rup x ρ) body')) as ->.
  { simpl_subst. f_equal. subst_ext i. depelim i ; simpl_subst ; reflexivity. }
  eapply pred1_app_beta ; eauto.
  rewrite All2_map. revert H3. apply All2_consequence. firstorder.
- reflexivity.
- reflexivity.
- now apply pred1_lam.
- now apply pred1_prod.
- apply pred1_app.
  + apply IHpred1.
  + revert H1. rewrite All2_map. apply All2_consequence. firstorder.
- reflexivity.
Qed.

(** Parallel reduction on substitutions is just pointwise parallel reduction. *)
Definition pred1_subst {s s'} (σ σ' : subst s s') : Prop :=
  forall i, pred1 (sapply σ i) (sapply σ' i).

#[export] Instance pred1_subst_Reflexive s s' : Reflexive (@pred1_subst s s').
Proof. intros σ i. reflexivity. Qed.

Lemma pred1_subst_scons {x s s'} t t' (σ σ' : subst s s') :
  pred1 t t' -> pred1_subst σ σ' -> pred1_subst (scons x t σ) (scons x t' σ').
Proof. intros Ht Hσ i. depelim i ; simpl_subst ; auto. Qed.

Lemma pred1_subst_sup {x s s'} (σ σ' : subst s s') :
  pred1_subst σ σ' -> pred1_subst (sup x σ) (sup x σ').
Proof.
intros H i. depelim i ; simpl_subst.
- reflexivity.
- apply pred1_rename. apply H.
Qed.

(** Substitution lemma for [pred1]. *)
Lemma pred1_substitute {s s'} (t t' : term s) (σ σ' : subst s s') :
  pred1 t t' ->
  pred1_subst σ σ' ->
  pred1 (substitute σ t) (substitute σ' t').
Proof.
intros Ht Hσ. induction Ht in s', σ, σ', Hσ |- * ; simpl_subst.
- cbn.
  assert (substitute (scomp (scons x arg' sid) σ') body' =
          substitute (scons x (substitute σ' arg') sid) (substitute (sup x σ') body')) as ->.
  { simpl_subst. f_equal. subst_ext i. depelim i ; simpl_subst ; reflexivity. }
  eapply pred1_app_beta ; eauto.
  + apply IHHt2. now apply pred1_subst_sup.
  + rewrite All2_map. revert H0. apply All2_consequence. firstorder.
- reflexivity.
- apply Hσ.
- apply pred1_lam ; auto. apply IHHt2. now apply pred1_subst_sup.
- apply pred1_prod ; auto. apply IHHt2. now apply pred1_subst_sup.
- apply pred1_app ; auto. rewrite All2_map. revert H0.
  apply All2_consequence. firstorder.
- reflexivity.
Qed.

(***********************************************************************)
(** * Diamond property for parallel reduction. *)
(***********************************************************************)

Lemma pred1_diamond {s} :
  diamond (@pred1 s) (@pred1 s).
Proof.
intros t u1 u2 H1 H2. depind H1.
- depelim H2.
  + apply IHpred1_1 in H2_. destruct H2_ as (vty & Hvty & Hvty').
    apply IHpred1_2 in H2_0. destruct H2_0 as (vbody & Hvbody & Hvbody').
    apply IHpred1_3 in H2_1. destruct H2_1 as (varg & Hvarg & Hvarg').
    assert (exists vargs, All2 pred1 args' vargs /\ All2 pred1 args'0 vargs) as (vargs & Hvargs & Hvargs').
    { admit. }
    exists (TApp (substitute (scons x varg sid) vbody) vargs). split.
    * apply pred1_app ; [apply pred1_substitute |] ; try assumption.
      now apply pred1_subst_scons.
    * apply pred1_app ; [apply pred1_substitute |] ; try assumption.
      now apply pred1_subst_scons.
  + admit.
- depelim H2. now eexists.
- depelim H2. now eexists.
- depelim H2. apply IHpred1_1 in H2_. apply IHpred1_2 in H2_0.
  destruct H2_ as (v & Hv1 & Hv2). destruct H2_0 as (u & Hu1 & Hu2).
  exists (TLam x v u). split ; apply pred1_lam ; assumption.
- depelim H2. apply IHpred1_1 in H2_. apply IHpred1_2 in H2_0.
  destruct H2_ as (v & Hv1 & Hv2). destruct H2_0 as (u & Hu1 & Hu2).
  exists (TProd x v u). split ; apply pred1_prod ; assumption.
- admit.
- depelim H2. now eexists.
Admitted.

Lemma pred1_confluence {s} :
  diamond (refl_trans_clos (@pred1 s)) (refl_trans_clos (@pred1 s)).
Proof. apply diamond_confluence, pred1_diamond. Qed.

(***********************************************************************)
(** * Main result: confluence. *)
(***********************************************************************)

(** Confluence for [red] is an immediate result of the confluence for [pred1]. *)
Lemma red_confluence {s} (t u1 u2 : term s) :
  red t u1 ->
  red t u2 ->
  exists v, red u1 v /\ red u2 v.
Proof.
intros H1 H2. rewrite red_is_pred in H1, H2.
pose proof (H := pred1_confluence t u1 u2 H1 H2).
destruct H as (v & Hv1 & Hv2). exists v. rewrite !red_is_pred. now split.
Qed.