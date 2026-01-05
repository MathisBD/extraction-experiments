From Metaprog Require Import Prelude.
From Metaprog.MetaTheory Require Export Substitution EvarMap RedFlags.

(** This module defines:
    - The one-step strong reduction relation [red1] on terms.
    - The strong reduction relation [red] on terms.
    And proves some basic properties, notably:
    - Congruence lemmas.
    - Inversion lemmas.
*)

(***********************************************************************)
(** * One-step reduction relation [red1]. *)
(***********************************************************************)

Reserved Notation "Σ ⊢ t ~>{ f } u"
  (at level 50, no associativity, t at next level, u at next level).

Unset Elimination Schemes.

(** Strong one-step reduction relation. This relation is _not_ deterministic. *)
Inductive red1 (flags : red_flags) (Σ : evar_map) {s} : term s -> term s -> Prop :=

(** Beta-reduction rule. *)
| red1_beta x ty body arg args :
    flags.(beta) = true ->
    Σ ⊢ TApp (TLam x ty body) (arg :: args) ~>{flags} TApp (body[x := arg]) args

(** Evar expansion. *)
| red1_evar_expand ev ty def :
    flags.(evars) = true ->
    Σ ev = Some (mk_evar_entry ty (Some def)) ->
    Σ ⊢ TEvar ev ~>{flags} wk def

(** Congrence rules for [TLam]. *)
| red1_lam_l x ty ty' body :
    Σ ⊢ ty ~>{flags} ty' -> Σ ⊢ TLam x ty body ~>{flags} TLam x ty' body
| red1_lam_r x ty body body' :
    Σ ⊢ body ~>{flags} body' -> Σ ⊢ TLam x ty body ~>{flags} TLam x ty body'

(** Congruence rules for [TProd]. *)
| red1_prod_l x a a' b :
    Σ ⊢ a ~>{flags} a' -> Σ ⊢ TProd x a b ~>{flags} TProd x a' b
| red1_prod_r x a b b' :
    Σ ⊢ b ~>{flags} b' -> Σ ⊢ TProd x a b ~>{flags} TProd x a b'

(** Congruence rules for [TApp]. *)
| red1_app_l f f' args :
    Σ ⊢ f ~>{flags} f' -> Σ ⊢ TApp f args ~>{flags} TApp f' args
| red1_app_r f args args' :
    OnOne2 (red1 flags Σ) args args' -> Σ ⊢ TApp f args ~>{flags} TApp f args'

where "Σ ⊢ t ~>{ f } u" := (red1 f Σ t u).

Set Elimination Schemes.

Derive Signature for red1.

Notation "Σ ⊢ t ~> u" := (red1 red_flags_all Σ t u)
  (at level 50, no associativity, t at next level, u at next level).

(***********************************************************************)
(** * Induction principle for [red1]. *)
(***********************************************************************)

(** Induction principle for [red1]. We can't use Rocq's default induction principle
    because [red1] is nested over [OnOne2]. *)
Lemma red1_ind (flags : red_flags) (Σ : evar_map) (P : forall s, term s -> term s -> Prop) :
  (forall s x ty body arg args,
    flags.(beta) = true ->
    P s (TApp (TLam x ty body) (arg :: args)) (TApp (body[x := arg]) args)) ->
  (forall s ev ty def,
    flags.(evars) = true ->
    Σ ev = Some (mk_evar_entry ty (Some def)) ->
    P s (TEvar ev) (wk def)) ->
  (forall s x ty ty' body,
    Σ ⊢ ty ~>{flags} ty' ->
    P s ty ty' ->
    P s (TLam x ty body) (TLam x ty' body)) ->
  (forall s x ty body body',
    Σ ⊢ body ~>{flags} body' ->
    P (s ▷ x) body body' ->
    P s (TLam x ty body) (TLam x ty body')) ->
  (forall s x a a' b,
    Σ ⊢ a ~>{flags} a' ->
    P s a a' ->
    P s (TProd x a b) (TProd x a' b)) ->
  (forall s x a b b',
    Σ ⊢ b ~>{flags} b' ->
    P (s ▷ x) b b' ->
    P s (TProd x a b) (TProd x a b')) ->
  (forall s f f' args,
    Σ ⊢ f ~>{flags} f' ->
    P s f f' ->
    P s (TApp f args) (TApp f' args)) ->
  (forall s f args args',
    OnOne2 (fun arg arg' => Σ ⊢ arg ~>{flags} arg' /\ P s arg arg') args args' ->
    P s (TApp f args) (TApp f args')) ->
  forall s t t', Σ ⊢ t ~>{flags} t' -> P s t t'.
Proof.
intros Hbeta Hevar Hlam_l Hlam_r Hprod_l Hprod_r Happ_l Happ_r. fix IH 4.
intros s t t' Hred. destruct Hred.
- apply Hbeta ; auto.
- eapply Hevar ; eauto.
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

Reserved Notation "Σ ⊢ t ~~>{ f } u"
  (at level 50, no associativity, t at next level, u at next level).

(** Strong reduction relation, defined as the reflexive-transitive closure of [red1]. *)
Inductive red (flags : red_flags) (Σ : evar_map) {s} : term s -> term s -> Prop :=
| red_refl t : Σ ⊢ t ~~>{flags} t
| red_step t1 t2 t3 : Σ ⊢ t1 ~~>{flags} t2 -> Σ ⊢ t2 ~>{flags} t3 -> Σ ⊢ t1 ~~>{flags} t3

where  "Σ ⊢ t ~~>{ f } u" := (red f Σ t u).

Derive Signature for red.

Notation "Σ ⊢ t ~~> u" := (red red_flags_all Σ t u)
  (at level 50, no associativity, t at next level, u at next level).

(***********************************************************************)
(** * Typeclass instances for setoid rewriting. *)
(***********************************************************************)

#[export] Instance red_Reflexive flags Σ s : Reflexive (@red flags Σ s).
Proof. intros t. apply red_refl. Qed.

#[export] Instance red_Transitive flags Σ s : Transitive (@red flags Σ s).
Proof.
intros t1 t2 t3 H1 H2. induction H2.
- assumption.
- apply red_step with t2 ; auto.
Qed.

#[export] Instance red_of_red1 flags Σ s :
  subrelation (@red1 flags Σ s) (@red flags Σ s).
Proof. intros t u H. apply red_step with t ; auto. apply red_refl. Qed.

Lemma red_same flags Σ {s} (t u : term s) :
  t = u -> Σ ⊢ t ~~>{flags} u.
Proof. intros ->. reflexivity. Qed.

Lemma red1_extend_flags {flags1 flags2 Σ s} :
  red_flags_incl flags1 flags2 ->
  subrelation (@red1 flags1 Σ s) (@red1 flags2 Σ s).
Proof.
intros Hf t u Hred. induction Hred ; try now constructor.
- constructor. now apply Hf.
- econstructor ; [now apply Hf |]. eassumption.
- constructor. revert H. apply OnOne2_consequence. firstorder.
Qed.

Lemma red_extend_flags {flags1 flags2 Σ s} :
  red_flags_incl flags1 flags2 ->
  subrelation (@red flags1 Σ s) (@red flags2 Σ s).
Proof.
intros Hf t u Hred. induction Hred.
- reflexivity.
- transitivity t2.
  + apply IHHred.
  + apply (red1_extend_flags Hf) in H. now rewrite H.
Qed.

(***********************************************************************)
(** * Congruence lemmas for [red1]. *)
(***********************************************************************)

Section CongruenceLemmas.
  Context (flags : red_flags) (Σ : evar_map) {s : scope}.

  Lemma red1_beta_alt x (ty : term s) body arg args t :
    flags.(beta) = true ->
    t = TApp (body[x := arg]) args ->
    Σ ⊢ TApp (TLam x ty body) (arg :: args) ~>{flags} t.
  Proof. intros H ->. now apply red1_beta. Qed.

  #[export] Instance red1_lam_congr_l x :
    Proper (red1 flags Σ ==> eq ==> red1 flags Σ) (@TLam s x).
  Proof. intros ty ty' Hty body body' <-. now apply red1_lam_l. Qed.

  #[export] Instance red1_lam_congr_r x :
    Proper (eq ==> red1 flags Σ ==> red1 flags Σ) (@TLam s x).
  Proof. intros ty ty' <- body body' Hbody. now apply red1_lam_r. Qed.

  #[export] Instance red1_prod_congr_l x :
    Proper (red1 flags Σ ==> eq ==> red1 flags Σ) (@TProd s x).
  Proof. intros ty ty' Hty body body' <-. now apply red1_prod_l. Qed.

  #[export] Instance red1_prod_congr_r x :
    Proper (eq ==> red1 flags Σ ==> red1 flags Σ) (@TProd s x).
  Proof. intros ty ty' <- body body' Hbody. now apply red1_prod_r. Qed.

  #[export] Instance red1_app_congr_l :
    Proper (red1 flags Σ ==> eq ==> red1 flags Σ) (@TApp s).
  Proof. intros f f' Hf args args' <-. now apply red1_app_l. Qed.

  #[export] Instance red1_app_congr_r :
    Proper (eq ==> OnOne2 (red1 flags Σ) ==> red1 flags Σ) (@TApp s).
  Proof. intros f f' <- args args' Hargs. now apply red1_app_r. Qed.

End CongruenceLemmas.

(***********************************************************************)
(** * Congruence lemmas for [red]. *)
(***********************************************************************)

Section CongruenceLemmas.
  Context (flags : red_flags) (Σ : evar_map) {s : scope}.

  Lemma red_beta x (ty : term s) body arg args :
    flags.(beta) = true ->
    Σ ⊢ TApp (TLam x ty body) (arg :: args) ~~>{flags} TApp (body[x := arg]) args.
  Proof. intros H. now rewrite red1_beta. Qed.

  Lemma red_evar_expand ev ty def :
    flags.(evars) = true ->
    Σ ev = Some (mk_evar_entry ty (Some def)) ->
    Σ ⊢ @TEvar s ev ~~>{flags} wk def.
  Proof. intros H1 H2. rewrite red1_evar_expand ; eauto. reflexivity. Qed.

  #[export] Instance red_lam_congr x :
    Proper (red flags Σ ==> red flags Σ ==> red flags Σ) (@TLam s x).
  Proof.
  intros ty ty' Hty body body' Hbody. transitivity (TLam x ty body').
  - clear Hty. induction Hbody.
    + reflexivity.
    + now rewrite <-H.
  - clear Hbody. induction Hty.
    + reflexivity.
    + now rewrite <-H.
  Qed.

  #[export] Instance red_prod_congr x :
    Proper (red flags Σ ==> red flags Σ ==> red flags Σ) (@TProd s x).
  Proof.
  intros a a' Ha b b' Hb. transitivity (TProd x a b').
  - clear Ha. induction Hb.
    + reflexivity.
    + now rewrite <-H.
  - clear Hb. induction Ha.
    + reflexivity.
    + now rewrite <-H.
  Qed.

  Lemma red_app_congr_aux (f : term s) l (args args' : list (term s)) :
    All2 (red flags Σ) args args' ->
    Σ ⊢ TApp f (l ++ args) ~~>{flags} TApp f (l ++ args').
  Proof.
  intros H. revert f l. depind H ; intros f l.
  - reflexivity.
  - transitivity (TApp f (l ++ y :: xs)).
    + clear IHAll2 H0. induction H.
      * reflexivity.
      * rewrite IHred. apply red_of_red1. f_equiv. now apply OnOne2_app_r, OnOne2_head.
    + specialize (IHAll2 f (l ++ [y])). rewrite <-!app_assoc in IHAll2.
      cbn in IHAll2. exact IHAll2.
  Qed.

  #[export] Instance red_app_congr :
    Proper (red flags Σ ==> All2 (red flags Σ) ==> red flags Σ) (@TApp s).
  Proof.
  intros f f' Hf args arg' Hargs. transitivity (TApp f' args).
  - clear Hargs. induction Hf.
    + reflexivity.
    + now rewrite <-H.
  - clear f Hf. apply red_app_congr_aux with (l := []). assumption.
  Qed.

End CongruenceLemmas.

(***********************************************************************)
(** * Inversion lemmas for [red]. *)
(***********************************************************************)

Section InversionLemmas.
  Context (flags : red_flags) (Σ : evar_map) {s : scope}.

  Lemma red_type_inv (t : term s) :
    Σ ⊢ TType ~~>{flags} t -> t = TType.
  Proof.
  intros H. depind H.
  - reflexivity.
  - subst. depelim H0.
  Qed.

  Lemma red_var_inv (i : index s) (t : term s) :
    Σ ⊢ TVar i ~~>{flags} t -> t = TVar i.
  Proof.
  intros H. depind H.
  - reflexivity.
  - subst. depelim H0.
  Qed.

  Lemma red_lam_inv x (ty : term s) body t :
    Σ ⊢ TLam x ty body ~~>{flags} t ->
    exists ty' body',
      t = TLam x ty' body' /\
      Σ ⊢ ty ~~>{flags} ty' /\
      Σ ⊢ body ~~>{flags} body'.
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
    Σ ⊢ TProd x a b ~~>{flags} t ->
    exists a' b',
      t = TProd x a' b' /\
      Σ ⊢ a ~~>{flags} a' /\
      Σ ⊢ b ~~>{flags} b'.
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
