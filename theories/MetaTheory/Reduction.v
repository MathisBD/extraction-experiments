From Metaprog Require Import Prelude.
From Metaprog.MetaTheory Require Export Relations Substitution EvarMap.

(** This module defines:
    - The one-step strong reduction relation [red1] on [term].
    - The strong reduction relation [red] on [term] and its basic properties. *)

(***********************************************************************)
(** * One-step reduction relation [red1]. *)
(***********************************************************************)

Reserved Notation "Σ ⊢ t ~>₁ u"
  (at level 50, no associativity, t at next level, u at next level).

Unset Elimination Schemes.

(** Strong one-step reduction relation. This relation is _not_ deterministic. *)
Inductive red1 {s} Σ : term s -> term s -> Prop :=

(** Beta-reduction rule. *)
| red1_beta x ty body arg args :
    Σ ⊢ TApp (TLam x ty body) (arg :: args) ~>₁ TApp (body[x := arg]) args

(** Evar expansion. *)
| red1_evar_expand ev ty def :
    Σ ev = Some (mk_evar_entry ty (Some def)) ->
    Σ ⊢ TEvar ev ~>₁ wk def

(** Congrence rules for [TLam]. *)
| red1_lam_l x ty ty' body :
    Σ ⊢ ty ~>₁ ty' -> Σ ⊢ TLam x ty body ~>₁ TLam x ty' body
| red1_lam_r x ty body body' :
    Σ ⊢ body ~>₁ body' -> Σ ⊢ TLam x ty body ~>₁ TLam x ty body'

(** Congruence rules for [TProd]. *)
| red1_prod_l x a a' b :
    Σ ⊢ a ~>₁ a' -> Σ ⊢ TProd x a b ~>₁ TProd x a' b
| red1_prod_r x a b b' :
    Σ ⊢ b ~>₁ b' -> Σ ⊢ TProd x a b ~>₁ TProd x a b'

(** Congruence rules for [TApp]. *)
| red1_app_l f f' args :
    Σ ⊢ f ~>₁ f' -> Σ ⊢ TApp f args ~>₁ TApp f' args
| red1_app_r f args args' :
    OnOne2 (red1 Σ) args args' -> Σ ⊢ TApp f args ~>₁ TApp f args'

where "Σ ⊢ t ~>₁ u" := (red1 Σ t u).

Set Elimination Schemes.

Derive Signature for red1.

(***********************************************************************)
(** * Induction principle for [red1]. *)
(***********************************************************************)

(** Induction principle for [red1]. We can't use Rocq's default induction principle
    because [red1] is nested over [OnOne2]. *)
Lemma red1_ind (P : forall s, evar_map -> term s -> term s -> Prop) :
  (forall s Σ x ty body arg args,
    P s Σ (TApp (TLam x ty body) (arg :: args)) (TApp (body[x := arg]) args)) ->
  (forall s Σ ev ty def,
    Σ ev = Some (mk_evar_entry ty (Some def)) ->
    P s Σ (TEvar ev) (wk def)) ->
  (forall s Σ x ty ty' body,
    Σ ⊢ ty ~>₁ ty' ->
    P s Σ ty ty' ->
    P s Σ (TLam x ty body) (TLam x ty' body)) ->
  (forall s Σ x ty body body',
    Σ ⊢ body ~>₁ body' ->
    P (s ▷ x) Σ body body' ->
    P s Σ (TLam x ty body) (TLam x ty body')) ->
  (forall s Σ x a a' b,
    Σ ⊢ a ~>₁ a' ->
    P s Σ a a' ->
    P s Σ (TProd x a b) (TProd x a' b)) ->
  (forall s Σ x a b b',
    Σ ⊢ b ~>₁ b' ->
    P (s ▷ x) Σ b b' ->
    P s Σ (TProd x a b) (TProd x a b')) ->
  (forall s Σ f f' args,
    Σ ⊢ f ~>₁ f' ->
    P s Σ f f' ->
    P s Σ (TApp f args) (TApp f' args)) ->
  (forall s Σ f args args',
    OnOne2 (fun arg arg' => Σ ⊢ arg ~>₁ arg' /\ P s Σ arg arg') args args' ->
    P s Σ (TApp f args) (TApp f args')) ->
  forall s Σ t t', Σ ⊢ t ~>₁ t' -> P s Σ t t'.
Proof.
intros Hbeta Hevar Hlam_l Hlam_r Hprod_l Hprod_r Happ_l Happ_r. fix IH 5.
intros s Σ t t' Hred. destruct Hred.
- apply Hbeta.
- eapply Hevar. eassumption.
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
Definition red {s} (Σ : evar_map) : term s -> term s -> Prop :=
  refl_trans_clos (@red1 s Σ).

Arguments red : simpl never.

Notation "Σ ⊢ t ~> u" := (red Σ t u)
  (at level 50, no associativity, t at next level, u at next level).

Lemma red_same {s} Σ (t u : term s) :
  t = u -> Σ ⊢ t ~> u.
Proof. intros ->. reflexivity. Qed.

Lemma red_of_red1 {s} Σ (t u : term s) :
  Σ ⊢ t ~>₁ u -> Σ ⊢ t ~> u.
Proof. apply refl_trans_clos_one. Qed.

#[export] Instance subrelation_red1_red s Σ :
  subrelation (@red1 s Σ) (@red s Σ).
Proof. intros t u H. now apply red_of_red1. Qed.

(***********************************************************************)
(** * Congruence lemmas. *)
(***********************************************************************)

Section CongruenceLemmas.
  Context {s : scope} (Σ : evar_map).

  Lemma red1_beta_alt x (ty : term s) body arg args t :
    t = TApp (body[x := arg]) args ->
    Σ ⊢ TApp (TLam x ty body) (arg :: args) ~>₁ t.
  Proof. intros ->. apply red1_beta. Qed.

  Lemma red_beta x (ty : term s) body arg args :
    Σ ⊢ TApp (TLam x ty body) (arg :: args) ~> TApp (body[x := arg]) args.
  Proof. now rewrite red1_beta. Qed.

  Lemma red_evar_expand ev ty def :
    Σ ev = Some (mk_evar_entry ty (Some def)) ->
    Σ ⊢ @TEvar s ev ~> wk def.
  Proof. intros H. rewrite red1_evar_expand ; eauto. reflexivity. Qed.

  #[export] Instance red_lam_congr x :
    Proper (red Σ ==> red Σ ==> red Σ) (@TLam s x).
  Proof.
  intros ty ty' Hty body body' Hbody. transitivity (TLam x ty body').
  - clear Hty. induction Hbody.
    + reflexivity.
    + rewrite IHHbody. now apply red_of_red1, red1_lam_r.
  - clear Hbody. induction Hty.
    + reflexivity.
    + rewrite IHHty. now apply red_of_red1, red1_lam_l.
  Qed.

  #[export] Instance red_prod_congr x :
    Proper (red Σ ==> red Σ ==> red Σ) (@TProd s x).
  Proof.
  intros a a' Ha b b' Hb. transitivity (TProd x a b').
  - clear Ha. induction Hb.
    + reflexivity.
    + rewrite IHHb. now apply red_of_red1, red1_prod_r.
  - clear Hb. induction Ha.
    + reflexivity.
    + rewrite IHHa. now apply red_of_red1, red1_prod_l.
  Qed.

  Lemma red_app_congr_aux (f : term s) l (args args' : list (term s)) :
    All2 (red Σ) args args' ->
    Σ ⊢ TApp f (l ++ args) ~> TApp f (l ++ args').
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

  #[export] Instance red_app_congr :
    Proper (red Σ ==> All2 (red Σ) ==> red Σ) (@TApp s).
  Proof.
  intros f f' Hf args arg' Hargs. transitivity (TApp f' args).
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
  Context {s : scope} (Σ : evar_map).

  Lemma red_type_inv (t : term s) :
    Σ ⊢ TType ~> t -> t = TType.
  Proof.
  intros H. depind H.
  - reflexivity.
  - subst. depelim H0.
  Qed.

  Lemma red_var_inv (i : index s) (t : term s) :
    Σ ⊢ TVar i ~> t -> t = TVar i.
  Proof.
  intros H. depind H.
  - reflexivity.
  - subst. depelim H0.
  Qed.

  Lemma red_lam_inv x (ty : term s) body t :
    Σ ⊢ TLam x ty body ~> t ->
    exists ty' body',
      t = TLam x ty' body' /\
      Σ ⊢ ty ~> ty' /\
      Σ ⊢ body ~> body'.
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
    Σ ⊢ TProd x a b ~> t ->
    exists a' b',
      t = TProd x a' b' /\
      Σ ⊢ a ~> a' /\
      Σ ⊢ b ~> b'.
  Proof.
  intros Hred. depind Hred.
  - exists a, b. now split3.
  - destruct IHHred as (a' & b' & -> & Ha1 & Hb1). depelim H.
    + exists a'0, b'. split3 ; [reflexivity | | assumption].
      rewrite Ha1. now apply red_of_red1.
    + exists a', b'0. split3 ; [reflexivity | assumption |].
      rewrite Hb1. now apply red_of_red1.
  Qed.

End InversionLemmas.

(***********************************************************************)
(** * Compatibility with renaming and substitution. *)
(***********************************************************************)

Section SubstitutionLemma.
  Context {s s' : scope} (Σ : evar_map).

  (** Renaming lemma for [red1]. *)
  #[export] Instance red1_rename (ρ : ren s s') :
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

  (** Renaming lemma for [red]. *)
  #[export] Instance red_rename (ρ : ren s s') :
    Proper (red Σ ==> red Σ) (rename ρ).
  Proof.
  intros t t' H. induction H.
  - reflexivity.
  - now rewrite IHrefl_trans_clos, H0.
  Qed.

  (** Substitution lemma for [red1]. *)
  #[export] Instance red1_substitute (σ : subst s s') :
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
  #[export] Instance red_substitute (σ : subst s s') :
    Proper (red Σ ==> red Σ) (substitute σ).
  Proof.
  intros t t' H. induction H.
  - reflexivity.
  - now rewrite IHrefl_trans_clos, H0.
  Qed.

End SubstitutionLemma.