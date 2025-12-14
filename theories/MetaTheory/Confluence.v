From Metaprog Require Import Prelude.
From Metaprog.MetaTheory Require Export Reduction.

(** This module proves the confluence lemma for the reduction relation [red]
    using the standard parallel reduction technique. *)

(***********************************************************************)
(** * Parallel reduction. *)
(***********************************************************************)

#[local] Reserved Notation "Σ ⊢ t >> u"
  (at level 50, no associativity, t at next level, u at next level).

Unset Elimination Schemes.

(** Parallel reduction relation. *)
Inductive pred1 {s} (Σ : evar_map) : term s -> term s -> Prop :=

(** Beta-reduction rule. *)
| pred1_app_beta x ty body body' arg arg' args args' :
    Σ ⊢ body >> body' ->
    Σ ⊢ arg >> arg' ->
    All2 (pred1 Σ) args args' ->
    Σ ⊢ TApp (TLam x ty body) (arg :: args) >> TApp (body'[x := arg']) args'

(** Evar expansion rule. *)
| pred1_evar_expand ev ty def :
    Σ ev = Some (mk_evar_entry ty (Some def)) ->
    Σ ⊢ TEvar ev >> wk def

(** Congruence rules. *)

| pred1_type :
    Σ ⊢ TType >> TType

| pred1_var i :
    Σ ⊢ TVar i >> TVar i

| pred1_lam x ty ty' body body' :
    Σ ⊢ ty >> ty' ->
    Σ ⊢ body >> body' ->
    Σ ⊢ TLam x ty body >> TLam x ty' body'

| pred1_prod x a a' b b' :
    Σ ⊢ a >> a' ->
    Σ ⊢ b >> b' ->
    Σ ⊢ TProd x a b >> TProd x a' b'

| pred1_app f f' args args' :
    Σ ⊢ f >> f' ->
    All2 (pred1 Σ) args args' ->
    Σ ⊢ TApp f args >> TApp f' args'

| pred1_evar ev :
    Σ ⊢ TEvar ev >> TEvar ev

where "Σ ⊢ t >> u" := (pred1 Σ t u).

Set Elimination Schemes.

Derive Signature for pred1.

#[export] Instance pred1_Reflexive s Σ :
  Reflexive (@pred1 s Σ).
Proof.
intros t. induction t using term_ind' ; constructor ; try assumption.
induction args ; constructor ; depelim H ; auto.
Qed.

(** Parallel reduction on substitutions is just pointwise parallel reduction. *)
Definition pred1_subst {s s'} Σ (σ σ' : subst s s') : Prop :=
  forall i, Σ ⊢ sapply σ i >> sapply σ' i.

Notation "Σ ⊢ σ1 >>ₛ σ2" := (pred1_subst Σ σ1 σ2)
  (at level 50, no associativity, σ1 at next level, σ2 at next level).

#[export] Instance pred1_subst_Reflexive s s' Σ :
  Reflexive (@pred1_subst s s' Σ).
Proof. intros σ i. reflexivity. Qed.

(***********************************************************************)
(** * Induction principle on [red1]. *)
(***********************************************************************)

(** Induction principle for [pred1]. We can't use Rocq's default induction principle
    because [pred1] is nested over [All2]. *)
Lemma pred1_ind (P : forall s, evar_map -> term s -> term s -> Prop)
  (Hbeta : forall s Σ x ty body body' arg arg' args args',
    Σ ⊢ body >> body' -> P (s ▷ x) Σ body body' ->
    Σ ⊢ arg >> arg' -> P s Σ arg arg' ->
    All2 (pred1 Σ) args args' -> All2 (P s Σ) args args' ->
    P s Σ (TApp (TLam x ty body) (arg :: args)) (TApp (body'[x := arg']) args'))
  (Hexpand : forall s Σ ev ty def,
    Σ ev = Some (mk_evar_entry ty (Some def)) ->
    P s Σ (TEvar ev) (wk def))
  (Htype : forall s Σ,
    P s Σ TType TType)
  (Hvar : forall s Σ i,
    P s Σ (TVar i) (TVar i))
  (Hlam : forall s Σ x ty ty' body body',
    Σ ⊢ ty >> ty' -> P s Σ ty ty' ->
    Σ ⊢ body >> body' -> P (s ▷ x) Σ body body' ->
    P s Σ (TLam x ty body) (TLam x ty' body'))
  (Hprod : forall s Σ x a a' b b',
    Σ ⊢ a >> a' -> P s Σ a a' ->
    Σ ⊢ b >> b' -> P (s ▷ x) Σ b b' ->
    P s Σ (TProd x a b) (TProd x a' b'))
  (Happ : forall s Σ f f' args args',
    Σ ⊢ f >> f' -> P s Σ f f' ->
    All2 (pred1 Σ) args args' -> All2 (P s Σ) args args' ->
    P s Σ (TApp f args) (TApp f' args'))
  (Hevar : forall s Σ ev,
    P s Σ (TEvar ev) (TEvar ev)) :
  forall s Σ t t', Σ ⊢ t >> t' -> P s Σ t t'.
Proof.
fix IH 5. intros s Σ t t' Hred. destruct Hred.
- apply Hbeta ; try assumption ; try now apply IH.
  revert args args' H. fix IHargs 3. intros args args' H. destruct H.
  + constructor.
  + constructor ; auto.
- apply Hexpand with ty. assumption.
- apply Htype.
- apply Hvar.
- apply Hlam ; auto.
- apply Hprod ; auto.
- apply Happ ; auto. revert args args' H. fix IHargs 3. intros args args' H. destruct H.
  + constructor.
  + constructor ; auto.
- apply Hevar.
Qed.

(***********************************************************************)
(** * Relating parallel reduction and standard reduction. *)
(***********************************************************************)

(** [pred1] admits the beta rule. *)
Lemma pred1_beta {s} Σ x (ty : term s) body arg args :
  Σ ⊢ TApp (TLam x ty body) (arg :: args) >> TApp (body[x := arg]) args.
Proof. now apply pred1_app_beta. Qed.

(** One-step reduction is included in parallel reduction. *)
Lemma pred1_of_red1 {s} Σ (t u : term s) :
  Σ ⊢ t ~> u -> Σ ⊢ t >> u.
Proof.
intros H. induction H.
- apply pred1_beta.
- eapply pred1_evar_expand ; eassumption.
- now apply pred1_lam.
- now apply pred1_lam.
- now apply pred1_prod.
- now apply pred1_prod.
- now apply pred1_app.
- apply pred1_app ; [reflexivity|]. apply All2_of_OnOne2 ; [typeclasses eauto|].
  revert H. apply OnOne2_consequence. firstorder.
Qed.

(** Parallel reduction is included in standard reduction. *)
Lemma red_of_pred1 {s} Σ (t u : term s) :
  Σ ⊢ t >> u -> Σ ⊢ t ~~> u.
Proof.
intros H. induction H.
- rewrite <-red_beta. apply red_app_congr.
  + now apply red_lam_congr.
  + now constructor.
- eapply red_evar_expand ; eassumption.
- reflexivity.
- reflexivity.
- now apply red_lam_congr.
- now apply red_prod_congr.
- now apply red_app_congr.
- reflexivity.
Qed.

(** The reflexive closure of [pred1] is equal to [red]. *)
Lemma red_is_pred {s} Σ (t u : term s) :
  Σ ⊢ t ~~> u <-> refl_trans_clos (pred1 Σ) t u.
Proof.
split ; revert t u ; apply refl_trans_clos_incl.
- intros t u H. apply refl_trans_clos_one. now apply pred1_of_red1.
- intros t u H. now apply red_of_pred1.
Qed.

(***********************************************************************)
(** * Compatibility with renaming and substitution. *)
(***********************************************************************)

Lemma pred1_app_beta_alt {s} Σ x (ty : term s) body body' arg arg' args args' t :
  Σ ⊢ body >> body' ->
  Σ ⊢ arg >> arg' ->
  All2 (pred1 Σ) args args' ->
  t = TApp (body' [x := arg']) args' ->
  Σ ⊢ TApp (TLam x ty body) (arg :: args) >> t.
Proof. intros H1 H2 H3 ->. now apply pred1_app_beta. Qed.

(** Renaming lemma for [pred1]. *)
#[export] Instance pred1_rename {s s'} Σ (ρ : ren s s') :
  Proper (pred1 Σ ==> pred1 Σ) (rename ρ).
Proof.
intros t t' H. induction H in s', ρ |- * ; simpl_subst.
- eapply pred1_app_beta_alt
    with (body' := rename (rup x ρ) body')
         (arg' := rename ρ arg')
         (args' := map (rename ρ) args').
  + auto.
  + auto.
  + change (All2 (pred1 Σ) (map (rename ρ) args) (map (rename ρ) args')).
    rewrite All2_map. revert H2. apply All2_consequence. firstorder.
  + now simpl_subst.
- econstructor ; eassumption.
- reflexivity.
- reflexivity.
- now apply pred1_lam.
- now apply pred1_prod.
- apply pred1_app.
  + apply IHpred1.
  + revert H1. rewrite All2_map. apply All2_consequence. firstorder.
- reflexivity.
Qed.

#[export] Instance pred1_scons {x s s'} Σ :
  Proper (pred1 Σ ==> pred1_subst Σ ==> pred1_subst Σ) (@scons s s' x).
Proof. intros t t' Ht σ σ' Hσ i. depelim i ; simpl_subst ; auto. Qed.

#[export] Instance pred1_sup {x s s'} Σ :
  Proper (pred1_subst Σ ==> pred1_subst Σ) (@sup s s' x).
Proof.
intros σ σ' H i. depelim i ; simpl_subst.
- reflexivity.
- apply pred1_rename. apply H.
Qed.

(** Substitution lemma for [pred1]. *)
#[export] Instance pred1_substitute {s s'} Σ :
  Proper (pred1_subst Σ ==> pred1 Σ ==> pred1 Σ) (@substitute s s').
Proof.
intros σ σ' Hσ t t' Ht. induction Ht in s', σ, σ', Hσ |- * ; simpl_subst.
- apply pred1_app_beta_alt
    with (body' := substitute (sup x σ') body')
         (arg' := substitute σ' arg')
         (args' := map (substitute σ') args').
  + apply IHHt1. now apply pred1_sup.
  + now apply IHHt2.
  + change (All2 (pred1 Σ) (map (substitute σ) args) (map (substitute σ') args')).
    rewrite All2_map. revert H0. apply All2_consequence. firstorder.
  + now simpl_subst.
- econstructor ; eauto.
- reflexivity.
- apply Hσ.
- apply pred1_lam ; auto. apply IHHt2. now apply pred1_sup.
- apply pred1_prod ; auto. apply IHHt2. now apply pred1_sup.
- apply pred1_app ; auto. rewrite All2_map. revert H0.
  apply All2_consequence. firstorder.
- reflexivity.
Qed.

(***********************************************************************)
(** * Joinability for parallel reduction. *)
(***********************************************************************)

(** Two terms are joinable if they have a common reduct for [pred1]. *)
Definition joinable {s} Σ (t1 t2 : term s) : Prop :=
  exists u, Σ ⊢ t1 >> u /\ Σ ⊢ t2 >> u.

#[export] Instance joinable_Reflexive s Σ :
  Reflexive (@joinable s Σ).
Proof. intros t. exists t. now split. Qed.

#[export] Instance joinable_Symmetric s Σ :
  Symmetric (@joinable s Σ).
Proof. intros t1 t2. unfold joinable. firstorder. Qed.

(** Two substitutions are joinable if they are pointwise joinable. *)
Definition joinable_subst {s s'} Σ (σ1 σ2 : subst s s') : Prop :=
  exists σ, Σ ⊢ σ1 >>ₛ σ /\ Σ ⊢ σ2 >>ₛ σ.

#[export] Instance joinable_subst_Reflexive s s' Σ :
  Reflexive (@joinable_subst s s' Σ).
Proof. intros σ. exists σ. split ; reflexivity. Qed.

#[export] Instance joinable_subst_Symmetric s s' Σ :
  Symmetric (@joinable_subst s s' Σ).
Proof. intros σ1 σ2 (σ & H1 & H2). exists σ. firstorder. Qed.

Lemma joinable_scons {x s s'} Σ t1 t2 (σ1 σ2 : subst s s') :
  joinable Σ t1 t2 ->
  joinable_subst Σ σ1 σ2 ->
  joinable_subst Σ (scons x t1 σ1) (scons x t2 σ2).
Proof.
intros (t & Ht1 & Ht2) (σ & Hσ1 & Hσ2). exists (scons x t σ).
split ; now apply pred1_scons.
Qed.

Lemma joinable_substitute {s s'} Σ (t1 t2 : term s) (σ1 σ2 : subst s s') :
  joinable Σ t1 t2 ->
  joinable_subst Σ σ1 σ2 ->
  joinable Σ (substitute σ1 t1) (substitute σ2 t2).
Proof.
intros (t & Ht1 & Ht2) (σ & Hσ1 & Hσ2). exists (substitute σ t).
split ; now apply pred1_substitute.
Qed.

Lemma joinable_lam {s x} Σ (ty1 ty2 : term s) body1 body2 :
  joinable Σ ty1 ty2 ->
  joinable Σ body1 body2 ->
  joinable Σ (TLam x ty1 body1) (TLam x ty2 body2).
Proof.
intros (ty & Hty1 & Hty2) (body & Hbody1 & Hbody2).
exists (TLam x ty body). split ; apply pred1_lam ; assumption.
Qed.

Lemma joinable_prod {s x} Σ (a1 a2 : term s) b1 b2 :
  joinable Σ a1 a2 ->
  joinable Σ b1 b2 ->
  joinable Σ (TProd x a1 b1) (TProd x a2 b2).
Proof.
intros (a & Ha1 & Ha2) (b & Hb1 & Hb2).
exists (TProd x a b). split ; apply pred1_prod ; assumption.
Qed.

Lemma joinable_list {s} Σ (args1 args2 : list (term s)) :
  All2 (joinable Σ) args1 args2 ->
  exists args, All2 (pred1 Σ) args1 args /\ All2 (pred1 Σ) args2 args.
Proof.
intros H. induction H.
- exists []. split ; constructor.
- destruct H as (z & Hx & Hy). destruct IHAll2 as (args & Hargs1 & Hargs2).
  exists (z :: args). split ; constructor ; assumption.
Qed.

Lemma joinable_app {s} Σ (f1 f2 : term s) args1 args2 :
  joinable Σ f1 f2 ->
  All2 (joinable Σ) args1 args2 ->
  joinable Σ (TApp f1 args1) (TApp f2 args2).
Proof.
intros (f & Hf1 & Hf2) Hargs. apply joinable_list in Hargs.
destruct Hargs as (args & Hargs1 & Hargs2).
exists (TApp f args). split ; apply pred1_app ; assumption.
Qed.

Lemma joinable_beta {s x} Σ ty2 body1 body2 (arg1 arg2 : term s) args1 args2 :
  joinable Σ body1 body2 ->
  joinable Σ arg1 arg2 ->
  All2 (joinable Σ) args1 args2 ->
  joinable Σ (TApp (body1[x := arg1]) args1) (TApp (TLam x ty2 body2) (arg2 :: args2)).
Proof.
intros (body & Hbody1 & Hbody2) (arg & Harg1 & Harg2) Hargs.
apply joinable_list in Hargs. destruct Hargs as (args & Hargs1 & Hargs2).
exists (TApp (body[x := arg]) args). split.
- apply pred1_app.
  + repeat f_equiv ; assumption.
  + assumption.
- now eapply pred1_app_beta.
Qed.

(***********************************************************************)
(** * Diamond property for parallel reduction. *)
(***********************************************************************)

(** Just a weird consequence lemma for [All2] needed to prove the diamond property. *)
Lemma All2_weird_consequence {A} (P Q R : A -> A -> Prop) xs ys zs :
  (forall x y z, P y x -> Q y z -> R x z) ->
  All2 P ys xs -> All2 Q ys zs -> All2 R xs zs.
Proof.
intros H HP HQ. revert zs HQ. depind HP ; intros zs HQ ; depelim HQ ; constructor.
- firstorder.
- firstorder.
Qed.

(** [pred1] has the diamond property. *)
Lemma pred1_diamond {s} Σ (t u1 u2 : term s) :
  Σ ⊢ t >> u1 -> Σ ⊢ t >> u2 -> joinable Σ u1 u2.
Proof.
intros H1 H2. depind H1 ; depelim H2 ; try reflexivity.
- apply joinable_app ; [apply joinable_substitute ; [| apply joinable_scons] |].
  + now apply IHpred1_1.
  + now apply IHpred1_2.
  + reflexivity.
  + revert H0 H1. apply All2_weird_consequence. firstorder.
- depelim H2. depelim H1. eapply joinable_beta.
  + now apply IHpred1_1.
  + now apply IHpred1_2.
  + revert H0 H2. apply All2_weird_consequence. firstorder.
- rewrite H in H0. depelim H0. reflexivity.
- exists (wk def). split ; [reflexivity |]. econstructor ; eassumption.
- apply joinable_lam ; auto.
- apply joinable_prod ; auto.
- depelim H1. depelim H. depelim H1.
  specialize (IHpred1 (TLam x ty' body')). feed IHpred1. { now apply pred1_lam. }
  destruct IHpred1 as (z & Hz1 & Hz2). depelim Hz1. depelim Hz2.
  apply inj_right_sigma in H3. depelim H3.
  symmetry. eapply joinable_beta.
  + eexists ; eauto.
  + symmetry. auto.
  + revert H4 H2. apply All2_weird_consequence. firstorder.
- apply joinable_app ; auto. revert H0 H3. apply All2_weird_consequence. firstorder.
- exists (wk def). split ; [|reflexivity]. econstructor ; eassumption.
Qed.

(** [pred1] is confluent. This is a consequence of the diamond property. *)
Lemma pred1_confluence {s} Σ :
  diamond (refl_trans_clos (@pred1 s Σ)) (refl_trans_clos (@pred1 s Σ)).
Proof. apply diamond_confluence. intros t u1 u2. apply pred1_diamond. Qed.

(***********************************************************************)
(** * Main result: confluence of [red]. *)
(***********************************************************************)

(** Confluence for [red] is an immediate result of the confluence for [pred1]. *)
Lemma red_confluence {s} Σ (t u1 u2 : term s) :
  Σ ⊢ t ~~> u1 ->
  Σ ⊢ t ~~> u2 ->
  exists v, Σ ⊢ u1 ~~> v /\ Σ ⊢ u2 ~~> v.
Proof.
intros H1 H2. rewrite red_is_pred in H1, H2.
pose proof (H := pred1_confluence Σ t u1 u2 H1 H2).
destruct H as (v & Hv1 & Hv2). exists v. rewrite !red_is_pred. now split.
Qed.