From Metaprog Require Import Prelude Relations.
From Metaprog.MetaTheory Require Export Reduction.ContextReduction.

(** This module proves the confluence lemma for the multi-step reduction
    relation using the standard parallel reduction technique.

    We prove confluence not only for reduction of terms [red],
    but also for reduction of substitutions [sred] and reduction
    of contexts [cred]. *)

(***********************************************************************)
(** * Parallel reduction on terms. *)
(***********************************************************************)

#[local] Reserved Notation "Σ ⊢ t >>{ f } u"
  (at level 50, no associativity, t at next level, u at next level).

Unset Elimination Schemes.

(** Parallel reduction relation. *)
Inductive pred1 (flags : red_flags) (Σ : evar_map) {s} : term s -> term s -> Prop :=

(** Beta-reduction rule. *)
| pred1_beta x ty body body' arg arg' args args' :
    flags.(beta) = true ->
    Σ ⊢ body >>{flags} body' ->
    Σ ⊢ arg >>{flags} arg' ->
    All2 (pred1 flags Σ) args args' ->
    Σ ⊢ TApp (TLam x ty body) (arg :: args) >>{flags} TApp (body'[x := arg']) args'

(** Evar expansion rule. *)
| pred1_evar_expand ev ty def :
    flags.(evars) = true ->
    Σ ev = Some (mk_evar_entry ty (Some def)) ->
    Σ ⊢ TEvar ev >>{flags} wk def

(** Remove empty applications. *)
| pred1_empty_app f f' :
    Σ ⊢ f >>{flags} f' ->
    Σ ⊢ TApp f [] >>{flags} f'

(** Merge nested applications. *)
| pred1_nested_app f f' args1 args1' args2 args2' :
    Σ ⊢ f >>{flags} f' ->
    All2 (pred1 flags Σ) args1 args1' ->
    All2 (pred1 flags Σ) args2 args2' ->
    Σ ⊢ TApp (TApp f args1) args2 >>{flags} TApp f' (args1' ++ args2')

(** Congruence rules. *)

| pred1_type :
    Σ ⊢ TType >>{flags} TType

| pred1_var i :
    Σ ⊢ TVar i >>{flags} TVar i

| pred1_lam x ty ty' body body' :
    Σ ⊢ ty >>{flags} ty' ->
    Σ ⊢ body >>{flags} body' ->
    Σ ⊢ TLam x ty body >>{flags} TLam x ty' body'

| pred1_prod x a a' b b' :
    Σ ⊢ a >>{flags} a' ->
    Σ ⊢ b >>{flags} b' ->
    Σ ⊢ TProd x a b >>{flags} TProd x a' b'

| pred1_app f f' args args' :
    Σ ⊢ f >>{flags} f' ->
    All2 (pred1 flags Σ) args args' ->
    Σ ⊢ TApp f args >>{flags} TApp f' args'

| pred1_evar ev :
    Σ ⊢ TEvar ev >>{flags} TEvar ev

where "Σ ⊢ t >>{ f } u" := (pred1 f Σ t u).

Set Elimination Schemes.

Derive Signature for pred1.

#[export] Instance pred1_Reflexive flags Σ s :
  Reflexive (@pred1 flags Σ s).
Proof.
intros t. induction t using term_ind' ; constructor ; try assumption.
induction args ; constructor ; depelim H ; auto.
Qed.

(***********************************************************************)
(** * Parallel reduction on substitutions. *)
(***********************************************************************)

(** Parallel reduction on substitutions is just pointwise parallel reduction. *)
Definition spred1 flags Σ {s s'} (σ σ' : subst s s') : Prop :=
  forall i, Σ ⊢ sapply σ i >>{flags} sapply σ' i.

#[export] Instance spred1_Reflexive flags Σ s s' :
  Reflexive (@spred1 flags Σ s s').
Proof. intros σ i. reflexivity. Qed.

(***********************************************************************)
(** * Induction principle on [pred1]. *)
(***********************************************************************)

(** Induction principle for [pred1]. We can't use Rocq's default induction principle
    because [pred1] is nested over [All2]. *)
Lemma pred1_ind flags Σ (P : forall s, term s -> term s -> Prop)
  (Hbeta : forall s x ty body body' arg arg' args args',
    flags.(beta) = true ->
    Σ ⊢ body >>{flags} body' -> P (s ▷ x) body body' ->
    Σ ⊢ arg >>{flags} arg' -> P s arg arg' ->
    All2 (pred1 flags Σ) args args' -> All2 (P s) args args' ->
    P s (TApp (TLam x ty body) (arg :: args)) (TApp (body'[x := arg']) args'))
  (Hexpand : forall s ev ty def,
    flags.(evars) = true ->
    Σ ev = Some (mk_evar_entry ty (Some def)) ->
    P s (TEvar ev) (wk def))
  (Hempty : forall s f f',
    Σ ⊢ f >>{flags} f' -> P s f f' ->
    P s (TApp f []) f')
  (Hnested : forall s f f' args1 args1' args2 args2',
    Σ ⊢ f >>{flags} f' -> P s f f' ->
    All2 (pred1 flags Σ) args1 args1' -> All2 (P s) args1 args1' ->
    All2 (pred1 flags Σ) args2 args2' -> All2 (P s) args2 args2' ->
    P s (TApp (TApp f args1) args2) (TApp f' (args1' ++ args2')))
  (Htype : forall s,
    P s TType TType)
  (Hvar : forall s i,
    P s (TVar i) (TVar i))
  (Hlam : forall s x ty ty' body body',
    Σ ⊢ ty >>{flags} ty' -> P s ty ty' ->
    Σ ⊢ body >>{flags} body' -> P (s ▷ x) body body' ->
    P s (TLam x ty body) (TLam x ty' body'))
  (Hprod : forall s x a a' b b',
    Σ ⊢ a >>{flags} a' -> P s a a' ->
    Σ ⊢ b >>{flags} b' -> P (s ▷ x) b b' ->
    P s (TProd x a b) (TProd x a' b'))
  (Happ : forall s f f' args args',
    Σ ⊢ f >>{flags} f' -> P s f f' ->
    All2 (pred1 flags Σ) args args' -> All2 (P s) args args' ->
    P s (TApp f args) (TApp f' args'))
  (Hevar : forall s ev,
    P s (TEvar ev) (TEvar ev)) :
  forall s t t', Σ ⊢ t >>{flags} t' -> P s t t'.
Proof.
fix IH 4. intros s t t' Hred. destruct Hred.
- apply Hbeta ; try assumption ; try now apply IH.
  revert args args' H0. fix IHargs 3. intros args args' H0.
  destruct H0 ; constructor ; auto.
- apply Hexpand with ty ; assumption.
- apply Hempty ; try assumption ; auto.
- apply Hnested ; try assumption ; auto.
  + revert args1 args1' H. fix IHargs 3. intros args1 args1' H.
    destruct H ; constructor ; auto.
  + revert args2 args2' H0. fix IHargs 3. intros args2 args2' H0.
    destruct H0 ; constructor ; auto.
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

Section RelatingPredRed.
  Context {flags : red_flags} {Σ : evar_map}.

  (** [pred1] admits the beta rule. *)
  (*Lemma pred1_beta {s} x (ty : term s) body arg args :
    flags.(beta) = true ->
    Σ ⊢ TApp (TLam x ty body) (arg :: args) >>{flags} TApp (body[x := arg]) args.
  Proof. intros H. now apply pred1_app_beta. Qed.*)

  (** One-step reduction is included in parallel reduction. *)
  Lemma pred1_of_red1 {s} (t u : term s) :
    Σ ⊢ t ~>{flags} u -> Σ ⊢ t >>{flags} u.
  Proof.
  intros H. induction H.
  - now apply pred1_beta.
  - eapply pred1_evar_expand ; eassumption.
  - now apply pred1_empty_app.
  - now apply pred1_nested_app.
  - now apply pred1_lam.
  - now apply pred1_lam.
  - now apply pred1_prod.
  - now apply pred1_prod.
  - now apply pred1_app.
  - apply pred1_app ; [reflexivity|]. apply All2_of_OnOne2 ; [typeclasses eauto|].
    revert H. apply OnOne2_consequence. firstorder.
  Qed.

  (** Parallel reduction is included in standard reduction. *)
  Lemma red_of_pred1 {s} (t u : term s) :
    Σ ⊢ t >>{flags} u -> Σ ⊢ t ~~>{flags} u.
  Proof.
  intros H. induction H.
  - rewrite <-red_beta. apply red_app_congr.
    + now apply red_lam_congr.
    + now constructor.
    + assumption.
  - eapply red_evar_expand ; eassumption.
  - now rewrite red1_empty_app.
  - rewrite red1_nested_app. f_equiv.
    + assumption.
    + now apply All2_app.
  - reflexivity.
  - reflexivity.
  - now apply red_lam_congr.
  - now apply red_prod_congr.
  - now apply red_app_congr.
  - reflexivity.
  Qed.

  (** The reflexive closure of [pred1] is equal to [red]. *)
  Lemma red_is_pred {s} (t u : term s) :
    Σ ⊢ t ~~>{flags} u <-> refl_trans_clos (pred1 flags Σ) t u.
  Proof.
  split ; intros H ; induction H.
  - reflexivity.
  - apply refl_trans_step with t2 ; auto. now apply pred1_of_red1.
  - reflexivity.
  - rewrite IHrefl_trans_clos. now apply red_of_pred1.
  Qed.

End RelatingPredRed.

(***********************************************************************)
(** * Compatibility with renaming and substitution. *)
(***********************************************************************)

Section Substitutivity.
  Context {flags : red_flags} {Σ : evar_map}.

  Lemma pred1_beta_alt {s} x (ty : term s) body body' arg arg' args args' t :
    flags.(beta) = true ->
    Σ ⊢ body >>{flags} body' ->
    Σ ⊢ arg >>{flags} arg' ->
    All2 (pred1 flags Σ) args args' ->
    t = TApp (body' [x := arg']) args' ->
    Σ ⊢ TApp (TLam x ty body) (arg :: args) >>{flags} t.
  Proof. intros Hf H1 H2 H3 ->. now apply pred1_beta. Qed.

  (** Renaming lemma for [pred1]. *)
  #[export] Instance pred1_rename {s s'} (ρ : ren s s') :
    Proper (pred1 flags Σ ==> pred1 flags Σ) (rename ρ).
  Proof.
  intros t t' H. induction H in s', ρ |- * ; simpl_subst.
  - eapply pred1_beta_alt
      with (body' := rename (rup x ρ) body')
           (arg' := rename ρ arg')
           (args' := map (rename ρ) args') ;
    auto.
    + change (All2 (pred1 flags Σ) (map (rename ρ) args) (map (rename ρ) args')).
      rewrite All2_map. revert H3. apply All2_consequence. firstorder.
    + now simpl_subst.
  - econstructor ; eassumption.
  - now apply pred1_empty_app.
  - rewrite map_app. apply pred1_nested_app ; auto.
    + rewrite All2_map. revert H1. apply All2_consequence. firstorder.
    + rewrite All2_map. revert H3. apply All2_consequence. firstorder.
  - reflexivity.
  - reflexivity.
  - now apply pred1_lam.
  - now apply pred1_prod.
  - apply pred1_app.
    + apply IHpred1.
    + revert H1. rewrite All2_map. apply All2_consequence. firstorder.
  - reflexivity.
  Qed.

  #[export] Instance pred1_scons {x s s'} :
    Proper (pred1 flags Σ ==> spred1 flags Σ ==> spred1 flags Σ) (@scons s s' x).
  Proof. intros t t' Ht σ σ' Hσ i. depelim i ; simpl_subst ; auto. Qed.

  #[export] Instance pred1_sup {x s s'} :
    Proper (spred1 flags Σ ==> spred1 flags Σ) (@sup s s' x).
  Proof.
  intros σ σ' H i. depelim i ; simpl_subst.
  - reflexivity.
  - apply pred1_rename. apply H.
  Qed.

  (** Substitution lemma for [pred1]. *)
  #[export] Instance pred1_substitute {s s'} :
    Proper (spred1 flags Σ ==> pred1 flags Σ ==> pred1 flags Σ) (@substitute s s').
  Proof.
  intros σ σ' Hσ t t' Ht. induction Ht in s', σ, σ', Hσ |- * ; simpl_subst.
  - apply pred1_beta_alt
      with (body' := substitute (sup x σ') body')
           (arg' := substitute σ' arg')
           (args' := map (substitute σ') args').
    + assumption.
    + apply IHHt1. now apply pred1_sup.
    + now apply IHHt2.
    + change (All2 (pred1 flags Σ) (map (substitute σ) args) (map (substitute σ') args')).
      rewrite All2_map. revert H1. apply All2_consequence. firstorder.
    + now simpl_subst.
  - econstructor ; eauto.
  - apply pred1_empty_app. now apply IHHt.
  - rewrite map_app. apply pred1_nested_app ; auto.
    + rewrite All2_map. revert H0. apply All2_consequence ; firstorder.
    + rewrite All2_map. revert H2. apply All2_consequence ; firstorder.
  - reflexivity.
  - apply Hσ.
  - apply pred1_lam ; auto. apply IHHt2. now apply pred1_sup.
  - apply pred1_prod ; auto. apply IHHt2. now apply pred1_sup.
  - apply pred1_app ; auto. rewrite All2_map. revert H0.
    apply All2_consequence. firstorder.
  - reflexivity.
  Qed.

End Substitutivity.

(***********************************************************************)
(** * Joinability for parallel reduction. *)
(***********************************************************************)

(** Two terms are joinable if they have a common reduct for [pred1]. *)
Definition joinable flags Σ {s} (t1 t2 : term s) : Prop :=
  exists u, Σ ⊢ t1 >>{flags} u /\ Σ ⊢ t2 >>{flags} u.

(** Two substitutions are joinable if they are pointwise joinable. *)
Definition joinable_subst flags Σ {s s'} (σ1 σ2 : subst s s') : Prop :=
  exists σ, spred1 flags Σ σ1 σ /\ spred1 flags Σ σ2 σ.

Section JoinabilityLemmas.
  Context {flags : red_flags} {Σ : evar_map}.

  #[export] Instance joinable_Reflexive s :
    Reflexive (@joinable flags Σ s).
  Proof. intros t. exists t. now split. Qed.

  #[export] Instance joinable_Symmetric s :
    Symmetric (@joinable flags Σ s).
  Proof. intros t1 t2. unfold joinable. firstorder. Qed.

  #[export] Instance joinable_subst_Reflexive s s' :
    Reflexive (@joinable_subst flags Σ s s').
  Proof. intros σ. exists σ. split ; reflexivity. Qed.

  #[export] Instance joinable_subst_Symmetric s s' :
    Symmetric (@joinable_subst flags Σ s s').
  Proof. intros σ1 σ2 (σ & H1 & H2). exists σ. firstorder. Qed.

  Lemma joinable_scons {x s s'} t1 t2 (σ1 σ2 : subst s s') :
    joinable flags Σ t1 t2 ->
    joinable_subst flags Σ σ1 σ2 ->
    joinable_subst flags Σ (scons x t1 σ1) (scons x t2 σ2).
  Proof.
  intros (t & Ht1 & Ht2) (σ & Hσ1 & Hσ2). exists (scons x t σ).
  split ; now apply pred1_scons.
  Qed.

  Lemma joinable_substitute {s s'} (t1 t2 : term s) (σ1 σ2 : subst s s') :
    joinable flags Σ t1 t2 ->
    joinable_subst flags Σ σ1 σ2 ->
    joinable flags Σ (substitute σ1 t1) (substitute σ2 t2).
  Proof.
  intros (t & Ht1 & Ht2) (σ & Hσ1 & Hσ2). exists (substitute σ t).
  split ; now apply pred1_substitute.
  Qed.

  Lemma joinable_lam {s x} (ty1 ty2 : term s) body1 body2 :
    joinable flags Σ ty1 ty2 ->
    joinable flags Σ body1 body2 ->
    joinable flags Σ (TLam x ty1 body1) (TLam x ty2 body2).
  Proof.
  intros (ty & Hty1 & Hty2) (body & Hbody1 & Hbody2).
  exists (TLam x ty body). split ; apply pred1_lam ; assumption.
  Qed.

  Lemma joinable_prod {s x} (a1 a2 : term s) b1 b2 :
    joinable flags Σ a1 a2 ->
    joinable flags Σ b1 b2 ->
    joinable flags Σ (TProd x a1 b1) (TProd x a2 b2).
  Proof.
  intros (a & Ha1 & Ha2) (b & Hb1 & Hb2).
  exists (TProd x a b). split ; apply pred1_prod ; assumption.
  Qed.

  Lemma joinable_list {s} (args1 args2 : list (term s)) :
    All2 (joinable flags Σ) args1 args2 ->
    exists args, All2 (pred1 flags Σ) args1 args /\ All2 (pred1 flags Σ) args2 args.
  Proof.
  intros H. induction H.
  - exists []. split ; constructor.
  - destruct H as (z & Hx & Hy). destruct IHAll2 as (args & Hargs1 & Hargs2).
    exists (z :: args). split ; constructor ; assumption.
  Qed.

  Lemma joinable_app {s} (f1 f2 : term s) args1 args2 :
    joinable flags Σ f1 f2 ->
    All2 (joinable flags Σ) args1 args2 ->
    joinable flags Σ (TApp f1 args1) (TApp f2 args2).
  Proof.
  intros (f & Hf1 & Hf2) Hargs. apply joinable_list in Hargs.
  destruct Hargs as (args & Hargs1 & Hargs2).
  exists (TApp f args). split ; apply pred1_app ; assumption.
  Qed.

  Lemma joinable_beta_l {s x} ty2 body1 body2 (arg1 arg2 : term s) args1 args2 :
    flags.(beta) = true ->
    joinable flags Σ body1 body2 ->
    joinable flags Σ arg1 arg2 ->
    All2 (joinable flags Σ) args1 args2 ->
    joinable flags Σ (TApp (body1[x := arg1]) args1) (TApp (TLam x ty2 body2) (arg2 :: args2)).
  Proof.
  intros Hf (body & Hbody1 & Hbody2) (arg & Harg1 & Harg2) Hargs.
  apply joinable_list in Hargs. destruct Hargs as (args & Hargs1 & Hargs2).
  exists (TApp (body[x := arg]) args). split.
  - apply pred1_app.
    + repeat f_equiv ; assumption.
    + assumption.
  - eapply pred1_beta ; eauto.
  Qed.

  Lemma joinable_empty_app_l {s} (t u : term s) :
    joinable flags Σ t u ->
    joinable flags Σ (TApp t []) u.
  Proof.
  intros (v & H1 & H2). exists v. split ; [|assumption]. now apply pred1_empty_app.
  Qed.

  Lemma joinable_empty_app_r {s} (t u : term s) :
    joinable flags Σ t u ->
    joinable flags Σ t (TApp u []).
  Proof. intros H. symmetry. now apply joinable_empty_app_l. Qed.

(*

t1 xs >> t2 ->?
t1 (xs ++ ys) >> apps t2 ys

beta reduction:
(λ body) (x :: xs) >> (body[x]) xs
(λ body) (x :: xs ++ ys) >> (body[x]) (xs ++ ys)

app reduction:
t1 xs >> t1' xs'
t1 (xs ++ ys) >> t1' (xs' ++ ys')

empty app reduction:
t1 [] >> t1
t1 ([] ++ ys) >> apps t1 ys    because (t xs >> apps t xs)

nested app reduction:
(t1 xs) xs' >> t1 (xs ++ xs')
(t1 xs) (xs' ++ ys) >> t1 (xs ++ xs' ++ ys)


(t []) [] >> t []
v            v
v            v
t     >>     t


*)

  (*Definition apps {s} (f : term s) (xs : list (term s)) : term s :=
    match f with
    | TApp f args => TApp f (args ++ xs)
    | _ => TApp f xs
    end.

  Lemma pred1_app_extend {s} (t1 t2 : term s) xs ys ys' :
    All2 (pred1 flags Σ) ys ys' ->
    Σ ⊢ TApp t1 xs >>{flags} t2 ->
    Σ ⊢ TApp t1 (xs ++ ys) >>{flags} apps t2 ys'.
  Proof.
  intros Hys H. depelim H ; cbn.
  - apply pred1_beta ; auto. now apply All2_app.
  - depelim H ; cbn.
    + apply pred1_nested_app.
  - rewrite <-app_assoc. apply pred1_nested_app ; auto. now apply All2_app.
  - apply pred1_app ; auto. now apply All2_app.*)

  Lemma aux1 {s x} ty t t' (arg arg' : term s) args1 args1' args2 args2' :
    flags.(beta) = true ->
    joinable flags Σ t t' ->
    joinable flags Σ arg arg' ->
    All2 (joinable flags Σ) args1 args1' ->
    All2 (joinable flags Σ) args2 args2' ->
    joinable flags Σ (TApp (TLam x ty t) (arg :: args1 ++ args2)) (TApp (TApp (t'[x := arg']) args1') args2').
  Proof.
  intros Hf (t0 & Ht & Ht') (arg0 & Harg & Harg') H1 H2.
  apply joinable_list in H1, H2.
  destruct H1 as (args1_0 & Hargs1 & Hargs1'). destruct H2 as (args2_0 & Hargs2 & Hargs2').
  exists (TApp (t0[x := arg0]) (args1_0 ++ args2_0)). split.
  - apply pred1_beta ; auto. now apply All2_app.
  - apply pred1_nested_app ; auto. apply pred1_substitute ; auto. now apply pred1_scons.
  Qed.

  Lemma aux2 {s} (t t' : term s) args1 args1' args2 args2' :
    joinable flags Σ t t' ->
    All2 (joinable flags Σ) args1 args1' ->
    All2 (joinable flags Σ) args2 args2' ->
    joinable flags Σ (TApp (TApp t args1) args2) (TApp t' (args1' ++ args2')).
  Proof.
  intros (t0 & Ht & Ht') H1 H2. apply joinable_list in H1, H2.
  destruct H1 as (args1_0 & Hargs1 & Hargs1'). destruct H2 as (args2_0 & Hargs2 & Hargs2').
  exists (TApp t0 (args1_0 ++ args2_0)). split.
  - apply pred1_nested_app ; auto.
  - apply pred1_app ; auto. now apply All2_app.
  Qed.


End JoinabilityLemmas.

(***********************************************************************)
(** * Diamond property for parallel reduction. *)
(***********************************************************************)

Section DiamondPred1.
  Context {flags : red_flags} {Σ : evar_map}.

  Lemma All2_joinable {s} {args args1 args2 : list (term s)} :
    All2 (pred1 flags Σ) args args1 ->
    All2 (pred1 flags Σ) args args2 ->
    Forall (diamond (pred1 flags Σ) (pred1 flags Σ)) args ->
    All2 (joinable flags Σ) args1 args2.
  Proof.
  revert args1 args2. induction args ; intros args1 args2 H1 H2 H.
  - depelim H1. depelim H2. constructor.
  - depelim H1. depelim H2. constructor.
    + depelim H3. now apply H3.
    + apply IHargs ; auto. now depelim H3.
  Qed.

  #[local] Ltac solve_size :=
    first [ assumption
          | (repeat first [ progress simp term_size sum | progress cbn ]) ; lia
          | idtac ].

  Lemma Forall_term_size s (P : term s -> Prop) args :
    (forall t, term_size t <= sum (map term_size args) -> P t) ->
    Forall P args.
  Proof.
  intros H. induction args ; constructor.
  - apply H. solve_size.
  - apply IHargs. intros t Ht. apply H. solve_size.
  Qed.

  (*Lemma joinable_app_extend {s} (t t' : term s) xs' ys ys' :
    joinable flags Σ t (TApp t' xs') ->
    All2 (joinable flags Σ) ys ys' ->
    joinable flags Σ (TApp t ys) (TApp t' (xs' ++ ys')).
  Proof.
  revert ys ys'.*)


  (** [pred1] has the diamond property. *)
  Lemma pred1_diamond {s} (t : term s) :
    diamond (pred1 flags Σ) (pred1 flags Σ) t.
  Proof.
  (* The proof is by induction on the size of [t], then inspecting
     the shape of both reductions from [t]. *)
  remember (term_size t) as n. revert s t Heqn. induction n using Wf_nat.lt_wf_ind.
  intros s t -> u1 u2 Hu1 Hu2.
  assert (IH : forall s (x : term s),
    term_size x < term_size t -> diamond (pred1 flags Σ) (pred1 flags Σ) x) by firstorder.
  clear H. change (joinable flags Σ u1 u2).
  depelim Hu1 ; depelim Hu2 ; try reflexivity.
  - apply joinable_app ; [apply joinable_substitute ; [| apply joinable_scons] |].
    + apply IH with body ; solve_size.
    + apply IH with arg ; solve_size.
    + reflexivity.
    + apply (All2_joinable H0 H2), Forall_term_size.
      intros t Ht. apply IH. solve_size.
  - depelim H1. depelim Hu2. eapply joinable_beta_l.
    + assumption.
    + apply IH with body ; solve_size.
    + apply IH with arg ; solve_size.
    + apply (All2_joinable H0 H2), Forall_term_size.
      intros t Ht. apply IH. solve_size.
  - rewrite H0 in H2. depelim H2. reflexivity.
  - exists (wk def). split ; [reflexivity |]. econstructor ; eassumption.
  - apply IH with f ; solve_size.
  - depelim H0. rewrite app_nil_r. apply IH with (TApp f0 args1) ; solve_size.
    now apply pred1_app.
  - depelim H. apply joinable_empty_app_r. apply IH with f ; solve_size.
  - depelim H0. rewrite app_nil_r. apply IH with (TApp f args1) ; solve_size.
    now apply pred1_app.
  - apply joinable_app ; [| apply All2_app].
    + apply IH with f ; solve_size.
    + apply (All2_joinable H H1), Forall_term_size.
      intros t Ht. apply IH. solve_size.
    + apply (All2_joinable H0 H2), Forall_term_size.
      intros t Ht. apply IH. solve_size.
  - admit.
  (*TApp f (args1 ++ args2) >> TApp f' (args1' ++ args2')
    TApp f (args1 ++ args2) >> apps f'0 args2'
  remember (term_size f'0) as n.
    revert args' args1 args1' args2 args2' f f' f'0 Heqn Hu1 H H0 Hu2 H1 IH.
    induction n using Wf_nat.lt_wf_ind. rename H into IHf.
    intros args' args1 args1' args2 args2' f f' f'0 -> Hu1 H H0 Hu2 H1 IH.
    depelim Hu2.
    + depelim Hu1. depelim H. cbn. apply aux1 ; auto.
      * apply IH with body ; solve_size.
      * apply IH with arg ; solve_size.
      * apply (All2_joinable H0 H3), Forall_term_size.
        intros t Ht. apply IH. solve_size.
      * apply (All2_joinable H1 H4), Forall_term_size.
        intros t Ht. apply IH. solve_size.
    + depelim H. cbn. apply IH with (TApp f args2) ; solve_size.
      * now apply pred1_app.
      * now apply pred1_app.
    + eapply IHf ; [| reflexivity | ..]. with (f := TApp f0 args0) ; [| reflexivity | ..]. ; auto.
    + symmetry. apply aux2.
      * apply IH with f ; solve_size.
      * apply (All2_joinable H1 H), Forall_term_size.
        intros t Ht. apply IH. solve_size.
      * apply (All2_joinable H2 H0), Forall_term_size.
        intros t Ht. apply IH. solve_size.
    (*+ depelim Hu1. depelim H. cbn. apply aux1 ; auto.
      * apply IH with body ; solve_size.
      * apply IH with arg ; solve_size.
      * apply (All2_joinable H0 H3), Forall_term_size.
        intros t Ht. apply IH. solve_size.
      * apply (All2_joinable H1 H4), Forall_term_size.
        intros t Ht. apply IH. solve_size.
    + depelim H. cbn. apply IH with (TApp f args2) ; solve_size.
      * now apply pred1_app.
      * now apply pred1_app.
    + admit.
    + symmetry. apply aux2.
      * apply IH with f ; solve_size.
      * apply (All2_joinable H1 H), Forall_term_size.
        intros t Ht. apply IH. solve_size.
      * apply (All2_joinable H2 H0), Forall_term_size.
        intros t Ht. apply IH. solve_size.*)*)
  - apply joinable_lam.
    + apply IH with ty ; solve_size.
    + apply IH with body ; solve_size.
  - apply joinable_prod.
    + apply IH with a ; solve_size.
    + apply IH with b ; solve_size.
  - depelim Hu1. depelim H. symmetry. eapply joinable_beta_l.
    + assumption.
    + apply IH with body ; solve_size.
    + apply IH with arg ; solve_size.
    + apply (All2_joinable H2 H0), Forall_term_size.
      intros t Ht. apply IH. solve_size.
  - depelim H. apply joinable_empty_app_l. apply IH with f ; solve_size.
  - admit.
  - apply joinable_app.
    + apply IH with f ; solve_size.
    + apply (All2_joinable H H0), Forall_term_size.
      intros t Ht. apply IH. solve_size.
  - exists (wk def). split ; [|reflexivity]. econstructor ; eassumption.
  Admitted.

End DiamondPred1.

(***********************************************************************)
(** * Main result: confluence of [red], [sred], and [cred]. *)
(***********************************************************************)

Section Confluence.
  Context {flags : red_flags} {Σ : evar_map}.

  (** Confluence for [red] is an immediate result of the diamond property for [pred1]. *)
  Lemma red_confluence {s} (t u1 u2 : term s) :
    Σ ⊢ t ~~>{flags} u1 ->
    Σ ⊢ t ~~>{flags} u2 ->
    exists v, Σ ⊢ u1 ~~>{flags} v /\ Σ ⊢ u2 ~~>{flags} v.
  Proof.
  intros H1 H2. setoid_rewrite red_is_pred. rewrite red_is_pred in H1, H2.
  eapply diamond_confluence with (R := @pred1 flags Σ s) ; eauto using pred1_diamond.
  Qed.

  (** Confluence for [sred] follows from confluence for [red]. *)
  Lemma sred_confluence {s s'} (σ τ1 τ2 : subst s s') :
    sred flags Σ σ τ1 ->
    sred flags Σ σ τ2 ->
    exists σ', sred flags Σ τ1 σ' /\ sred flags Σ τ2 σ'.
  Proof.
  intros H1 H2. induction s in s', σ, τ1, τ2, H1, H2 |- *.
  - exists (sren wk_idx). split ; constructor ; intros i ; depelim i.
  - specialize (IHs s' (rscomp rshift σ) (rscomp rshift τ1) (rscomp rshift τ2)).
    forward IHs. { now rewrite H1. }
    forward IHs. { now rewrite H2. }
    destruct IHs as (σ' & Hσ1 & Hσ2).
    assert (exists t, Σ ⊢ sapply τ1 I0 ~~>{flags} t /\ Σ ⊢ sapply τ2 I0 ~~>{flags} t) as (t & Ht1 & Ht2).
    {
      apply red_confluence with (sapply σ I0).
      - now rewrite H1.
      - now rewrite H2.
    }
    exists (scons x t σ'). split ; constructor ; intros i ; depelim i ; simpl_subst.
    + apply Ht1.
    + apply Hσ1.
    + apply Ht2.
    + apply Hσ2.
  Qed.

  (** Confluence for [cred] follows from confluence for [red]. *)
  Lemma cred_confluence {s} (Γ Γ1 Γ2 : context ∅ s) :
    cred flags Σ Γ Γ1 ->
    cred flags Σ Γ Γ2 ->
    exists Γ', cred flags Σ Γ1 Γ' /\ cred flags Σ Γ2 Γ'.
  Proof.
  intros H1 H2. induction s in Γ, Γ1, Γ2, H1, H2 |- *.
  - depelim Γ ; depelim Γ1 ; depelim Γ2. exists CNil. split ; constructor.
  - depelim H1. depelim H2.
    destruct (IHs _ _ _ H1 H2) as (Γ1 & HΓ & HΓ').
    assert (exists ty1, Σ ⊢ ty' ~~>{flags} ty1 /\ Σ ⊢ ty'0 ~~>{flags} ty1) as (ty1 & Hty1 & Hty2).
    { now apply red_confluence with ty. }
    exists (CCons Γ1 x ty1). split ; constructor ; auto.
  Qed.

End Confluence.
