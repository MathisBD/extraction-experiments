From Metaprog Require Import Prelude.
From Metaprog Require Export Data.Term.

(** This module develops the equational theory of renamings, thinnings, and substitutions,
    i.e. sigma calculus. Note that we assume the functional extensionality axiom which
    simplifies many lemmas.

    We provide a few tactics to reason about renamings and substitutions:
    - [ren_ext i] and [subst_ext i] are the analogs of [fun_ext i] for renamings
      and substitutions.
    - [simpl_subst] repeatedly rewrites with lemmas which simplify renamings
      and substitutions. A version [simpl_subst in H] is also available to
      simplify in hypothesis [H].
*)

(***********************************************************************)
(** * Extensionality lemmas. *)
(***********************************************************************)

Lemma ren_ext {s s'} (ρ ρ' : ren s s') :
  (forall i, rapply ρ i = rapply ρ' i) -> ρ = ρ'.
Proof.
intros H. destruct ρ ; destruct ρ'. f_equal. fun_ext i. apply H.
Qed.

Lemma thinning_ext {s s'} (δ δ' : thinning s s') :
  (forall i, tapply δ i = tapply δ' i) -> δ = δ'.
Proof.
intros H. depind δ.
- depelim δ'. reflexivity.
- depelim δ'.
  + f_equal. apply IHδ. intros i. specialize (H i). simp tapply in H. now depelim H.
  + specialize (H I0). simp tapply in H. depelim H.
- depelim δ'.
  + specialize (H I0). simp tapply in H. depelim H.
  + admit. (* Equations generates a very weird goal here. *)
Admitted.

Lemma subst_ext {s s'} (σ σ' : subst s s') :
  (forall i, sapply σ i = sapply σ' i) -> σ = σ'.
Proof.
intros H. destruct σ ; destruct σ'. f_equal. fun_ext i. apply H.
Qed.

(** Extentionality tactic for renamings. *)
Tactic Notation "ren_ext" ident(i) := apply ren_ext ; intros i.

(** Extentionality tactic for thinnings. *)
Tactic Notation "thinning_ext" ident(i) := apply thinning_ext ; intros i.

(** Extentionality tactic for substitutions. *)
Tactic Notation "subst_ext" ident(i) := apply subst_ext ; intros i.

(***********************************************************************)
(** * [simpl_subst] tactic. *)
(***********************************************************************)

(** [simpl_subst] uses the hint database [subst] to allow for easy extension.

    We are quite conservative in which lemmas we put in the [subst] database,
    because [simpl_subst] can easily loop indefinitely if we aren't careful. *)
Ltac simpl_subst :=
  repeat progress (rewrite_strat (bottomup (hints subst))).

Ltac simpl_subst_in H :=
  repeat progress (rewrite_strat (bottomup (hints subst)) in H).

Tactic Notation "simpl_subst" "in" ident(H) :=
  simpl_subst_in H.

#[export] Hint Rewrite
  rename_equation_1
  rename_equation_2
  rename_equation_3
  rename_equation_4
  rename_equation_5
  rename_equation_6
  : subst.

#[export] Hint Rewrite
  substitute_equation_1
  substitute_equation_2
  substitute_equation_3
  substitute_equation_4
  substitute_equation_5
  substitute_equation_6
  : subst.

Lemma map_nil {A B} (f : A -> B) :
  map f [] = [].
Proof. reflexivity. Qed.
#[export] Hint Rewrite @map_nil : subst.

#[export] Hint Rewrite app_nil_l : subst.
#[export] Hint Rewrite app_nil_r : subst.

(***********************************************************************)
(** * Lemmas about [apps]. *)
(***********************************************************************)

(*Lemma apps_tapp {s} (f : term s) args args' :
  apps (TApp f args) args' = TApp f (args ++ args').
Proof. simp apps. reflexivity. Qed.
#[export] Hint Rewrite @apps_tapp : subst.

Lemma apps_apps {s} (f : term s) args args' :
  apps (apps f args) args' = apps f (args ++ args').
Proof.
destruct f ; simp apps ; try reflexivity. now rewrite app_assoc.
Qed.
#[export] Hint Rewrite @apps_apps : subst.

Lemma rename_apps {s s'} (ρ : ren s s') f args :
  rename ρ (apps f args) = apps (rename ρ f) (map (rename ρ) args).
Proof.
destruct f ; cbn ; simp apps ; simpl_subst ; auto.
f_equal. rewrite map_app. reflexivity.
Qed.
#[export] Hint Rewrite @rename_apps : subst.

Lemma substitute_apps {s s'} (σ : subst s s') f args :
  substitute σ (apps f args) = apps (substitute σ f) (map (substitute σ) args).
Proof.
destruct f ; cbn ; simp apps ; simpl_subst ; auto.
f_equal. rewrite map_app. reflexivity.
Qed.
#[export] Hint Rewrite @substitute_apps : subst.*)

(***********************************************************************)
(** * Lemmas about [rapply]. *)
(***********************************************************************)

Lemma rapply_rid {s} i :
  rapply (@rid s) i = i.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @rapply_rid : subst.

Lemma rapply_rshift {s x} i :
  rapply (@rshift s x) i = IS i.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @rapply_rshift : subst.

Lemma rapply_rcomp {s s' s''} (ρ1 : ren s s') (ρ2 : ren s' s'') i :
  rapply (rcomp ρ1 ρ2) i = rapply ρ2 (rapply ρ1 i).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @rapply_rcomp : subst.

Lemma rapply_rcons_zero {s s' x} i (ρ : ren s s') :
  rapply (rcons x i ρ) I0 = i.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @rapply_rcons_zero : subst.

Lemma rapply_rcons_succ {s s' x} i (ρ : ren s s') j :
  rapply (rcons x i ρ) (IS j) = rapply ρ j.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @rapply_rcons_succ : subst.

Lemma rapply_rup_zero {s s' x} (ρ : ren s s') :
  rapply (rup x ρ) I0 = I0.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @rapply_rup_zero : subst.

Lemma rapply_rup_succ {s s' x} i (ρ : ren s s') :
  rapply (rup x ρ) (IS i) = IS (rapply ρ i).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @rapply_rup_succ : subst.

(***********************************************************************)
(** * Lemmas about renamings. *)
(***********************************************************************)

Lemma rcomp_rid_l {s s'} (ρ : ren s s') :
  rcomp rid ρ = ρ.
Proof. ren_ext i. rewrite rapply_rcomp, rapply_rid. reflexivity. Qed.
#[export] Hint Rewrite @rcomp_rid_l : subst.

Lemma rcomp_rid_r {s s'} (ρ : ren s s') :
  rcomp ρ rid = ρ.
Proof. ren_ext i. rewrite rapply_rcomp, rapply_rid. reflexivity. Qed.
#[export] Hint Rewrite @rcomp_rid_r : subst.

Lemma rup_rid {s x} :
  rup x (@rid s) = rid.
Proof. ren_ext i. depelim i ; reflexivity. Qed.
#[export] Hint Rewrite @rup_rid : subst.

Lemma rup_rcomp {x s s' s''} (ρ1 : ren s s') (ρ2 : ren s' s'') :
  rup x (rcomp ρ1 ρ2) = rcomp (rup x ρ1) (rup x ρ2).
Proof. ren_ext i. depelim i ; reflexivity. Qed.

Lemma rcons_zero_rshift {x s} :
  rcons x I0 (@rshift s x) = rid.
Proof. ren_ext i. depelim i ; simpl_subst ; reflexivity. Qed.
#[export] Hint Rewrite @rcons_zero_rshift : subst.

Lemma rcomp_rshift_rcons {x s s'} i (ρ : ren s s') :
  rcomp rshift (rcons x i ρ) = ρ.
Proof. ren_ext j. simpl_subst. reflexivity. Qed.
#[export] Hint Rewrite @rcomp_rshift_rcons : subst.

Lemma rcomp_rshift_rup {x s s'} (ρ : ren s s') :
  rcomp rshift (rup x ρ) = rcomp ρ rshift.
Proof. ren_ext i. simpl_subst. reflexivity. Qed.
#[export] Hint Rewrite @rcomp_rshift_rup : subst.

Lemma rename_rid {s} t :
  rename (@rid s) t = t.
Proof.
induction t using term_ind' ; simpl_subst ; f_equal ; try assumption.
clear IHt. induction args ; cbn.
- reflexivity.
- depelim H. rewrite H. unfold id. f_equal. now apply IHargs.
Qed.
#[export] Hint Rewrite @rename_rid : subst.

Lemma rename_rid' {s} :
  rename (@rid s) = id.
Proof. fun_ext t. now apply rename_rid. Qed.
#[export] Hint Rewrite @rename_rid' : subst.

Lemma rename_rename {s s' s''} (ρ1 : ren s s') (ρ2 : ren s' s'') t :
  rename ρ2 (rename ρ1 t) = rename (rcomp ρ1 ρ2) t.
Proof.
induction t in s', s'', ρ1, ρ2 |- * using term_ind' ; simpl_subst ; f_equal.
- apply IHt1.
- rewrite rup_rcomp. apply IHt2.
- apply IHt1.
- rewrite rup_rcomp. apply IHt2.
- apply IHt.
- induction H ; cbn ; f_equal.
  + apply H.
  + apply IHForall.
Qed.
#[export] Hint Rewrite @rename_rename : subst.

Lemma rcomp_assoc {s s' s'' s'''} (ρ1 : ren s s') (ρ2 : ren s' s'') (ρ3 : ren s'' s''') :
  rcomp (rcomp ρ1 ρ2) ρ3 = rcomp ρ1 (rcomp ρ2 ρ3).
Proof. ren_ext i. simpl_subst. reflexivity. Qed.
#[export] Hint Rewrite @rcomp_assoc : subst.

Lemma rcomp_rcons_l {x s s' s''} i (ρ1 : ren s s') (ρ2 : ren s' s'') :
  rcomp (rcons x i ρ1) ρ2 = rcons x (rapply ρ2 i) (rcomp ρ1 ρ2).
Proof. ren_ext j. depelim j ; simpl_subst ; reflexivity. Qed.
#[export] Hint Rewrite @rcomp_rcons_l : subst.

Lemma rcomp_rup_l {x s s' s''} (ρ1 : ren s s') (ρ2 : ren (s' ▷ x) s'') :
  rcomp (rup x ρ1) ρ2 = rcons x (rapply ρ2 I0) (rcomp (rcomp ρ1 rshift) ρ2).
Proof. ren_ext i. depelim i ; simpl_subst ; reflexivity. Qed.
#[export] Hint Rewrite @rcomp_rup_l : subst.

(***********************************************************************)
(** * Renamings and closed terms. *)
(***********************************************************************)

Lemma ren_closed {s} (ρ : ren ∅ s) :
  ρ = wk_idx.
Proof. ren_ext i. depelim i. Qed.

Lemma rename_closed {s} (ρ : ren ∅ s) (t : term ∅) :
  rename ρ t = wk t.
Proof. rewrite (ren_closed ρ). reflexivity. Qed.

Lemma rename_wk_closed {s s'} (ρ : ren s s') (t : term ∅) :
  rename ρ (wk t) = wk t.
Proof.
unfold wk. simpl_subst. rewrite (ren_closed (rcomp wk_idx ρ)). reflexivity.
Qed.
#[export] Hint Rewrite @rename_wk_closed : subst.

(***********************************************************************)
(** * Lemmas about [sapply]. *)
(***********************************************************************)

Lemma sapply_sid {s} i :
  sapply (@sid s) i = TVar i.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_sid : subst.

Lemma sapply_sshift {s x} i :
  sapply (@sshift s x) i = TVar (IS i).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_sshift : subst.

Lemma sapply_srcomp {s s' s''} (σ : subst s s') (ρ : ren s' s'') i :
  sapply (srcomp σ ρ) i = rename ρ (sapply σ i).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_srcomp : subst.

Lemma sapply_rscomp {s s' s''} (ρ : ren s s') (σ : subst s' s'') i :
  sapply (rscomp ρ σ) i = sapply σ (rapply ρ i).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_rscomp : subst.

Lemma sapply_scomp {s s' s''} (σ1 : subst s s') (σ2 : subst s' s'') i :
  sapply (scomp σ1 σ2) i = substitute σ2 (sapply σ1 i).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_scomp : subst.

Lemma sapply_scons_zero {s s' x} t (σ : subst s s') :
  sapply (scons x t σ) I0 = t.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_scons_zero : subst.

Lemma sapply_scons_succ {s s' x} t (σ : subst s s') i :
  sapply (scons x t σ) (IS i) = sapply σ i.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_scons_succ : subst.

Lemma sapply_sup_zero {s s' x} (σ : subst s s') :
  sapply (sup x σ) I0 = TVar I0.
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_sup_zero : subst.

Lemma sapply_sup_succ {s s' x} i (σ : subst s s') :
  sapply (sup x σ) (IS i) = rename rshift (sapply σ i).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_sup_succ : subst.

(***********************************************************************)
(** * Lemmas about [srcomp]. *)
(***********************************************************************)

Lemma sup_srcomp {s s' s'' x} (σ : subst s s') (ρ : ren s' s'') :
  sup x (srcomp σ ρ) = srcomp (sup x σ) (rup x ρ).
Proof.
subst_ext i. depelim i ; simpl_subst.
- reflexivity.
- reflexivity.
Qed.

Lemma rename_substitute {s s' s''} (σ : subst s s') (ρ : ren s' s'') t :
  rename ρ (substitute σ t) = substitute (srcomp σ ρ) t.
Proof.
induction t using term_ind' in s', s'', σ, ρ |- * ; simpl_subst.
- reflexivity.
- reflexivity.
- rewrite sup_srcomp. f_equal ; auto.
- rewrite sup_srcomp. f_equal ; auto.
- f_equal ; auto. clear IHt. induction H ; cbn.
  + reflexivity.
  + rewrite H, IHForall. reflexivity.
- reflexivity.
Qed.
#[export] Hint Rewrite @rename_substitute : subst.

Lemma srcomp_rid {s s'} (σ : subst s s') :
  srcomp σ rid = σ.
Proof. subst_ext i. simpl_subst. reflexivity. Qed.
#[export] Hint Rewrite @srcomp_rid : subst.

Lemma srcomp_assoc {s s' s'' s'''} (σ1 : subst s s') (σ2 : subst s' s'') (ρ3 : ren s'' s''') :
  srcomp (scomp σ1 σ2) ρ3 = scomp σ1 (srcomp σ2 ρ3).
Proof. subst_ext i. simpl_subst. reflexivity. Qed.
#[export] Hint Rewrite @srcomp_assoc : subst.

(***********************************************************************)
(** * Lemmas about [rscomp]. *)
(***********************************************************************)

Lemma rscomp_rid {s s'} (σ : subst s s') :
  rscomp rid σ = σ.
Proof. subst_ext i. simpl_subst. reflexivity. Qed.
#[export] Hint Rewrite @rscomp_rid : subst.

Lemma rscomp_rshift_scons {x s s'} t (σ : subst s s') :
  rscomp rshift (scons x t σ) = σ.
Proof. subst_ext i. simpl_subst. reflexivity. Qed.
#[export] Hint Rewrite @rscomp_rshift_scons : subst.

Lemma rscomp_rshift_sup {x s s'} (σ : subst s s') :
  rscomp rshift (sup x σ) = srcomp σ rshift.
Proof. subst_ext i. simpl_subst. reflexivity. Qed.
#[export] Hint Rewrite @rscomp_rshift_sup : subst.

Lemma sup_rscomp {s s' s'' x} (ρ : ren s s') (σ : subst s' s'') :
  sup x (rscomp ρ σ) = rscomp (rup x ρ) (sup x σ).
Proof.
subst_ext i. depelim i ; simpl_subst.
- reflexivity.
- reflexivity.
Qed.
#[export] Hint Rewrite @sup_srcomp : subst.

Lemma substitute_rename {s s' s''} (ρ : ren s s') (σ : subst s' s'') t :
  substitute σ (rename ρ t) = substitute (rscomp ρ σ) t.
Proof.
induction t using term_ind' in s', s'', σ, ρ |- * ; simpl_subst.
- reflexivity.
- reflexivity.
- rewrite sup_rscomp. f_equal ; auto.
- rewrite sup_rscomp. f_equal ; auto.
- f_equal ; auto. clear IHt. induction H ; cbn.
  + constructor.
  + rewrite H, IHForall. reflexivity.
- reflexivity.
Qed.
#[export] Hint Rewrite @substitute_rename : subst.

Lemma rscomp_assoc {s s' s'' s'''} (ρ1 : ren s s') (σ2 : subst s' s'') (σ3 : subst s'' s''') :
  scomp (rscomp ρ1 σ2) σ3 = rscomp ρ1 (scomp σ2 σ3).
Proof. subst_ext i. simpl_subst. reflexivity. Qed.
#[export] Hint Rewrite @rscomp_assoc : subst.

(***********************************************************************)
(** * Lemmas about [scomp]. *)
(***********************************************************************)

Lemma sup_sid {s x} :
  sup x (@sid s) = sid.
Proof. subst_ext i. depelim i ; reflexivity. Qed.
#[export] Hint Rewrite @sup_sid : subst.

Lemma sup_scomp {x s s' s''} (σ1 : subst s s') (σ2 : subst s' s'') :
  sup x (scomp σ1 σ2) = scomp (sup x σ1) (sup x σ2).
Proof. subst_ext i. depelim i ; simpl_subst ; reflexivity. Qed.
#[export] Hint Rewrite @sup_scomp : subst.

Lemma substitute_sid {s} t :
  substitute (@sid s) t = t.
Proof.
induction t using term_ind' ; simpl_subst ; f_equal ; try assumption.
clear IHt. induction H ; cbn.
- reflexivity.
- now rewrite H, IHForall.
Qed.
#[export] Hint Rewrite @substitute_sid : subst.

Lemma scomp_sid_l {s s'} (σ : subst s s') :
  scomp sid σ = σ.
Proof. subst_ext i. simpl_subst. reflexivity. Qed.
#[export] Hint Rewrite @scomp_sid_l : subst.

Lemma scomp_sid_r {s s'} (σ : subst s s') :
  scomp σ sid = σ.
Proof. subst_ext i. simpl_subst. reflexivity. Qed.
#[export] Hint Rewrite @scomp_sid_r : subst.

Lemma substitute_substitute {s s' s''} (σ1 : subst s s') (σ2 : subst s' s'') t :
  substitute σ2 (substitute σ1 t) = substitute (scomp σ1 σ2) t.
Proof.
induction t in s', s'', σ1, σ2 |- * using term_ind' ; simpl_subst ; f_equal ; auto.
clear IHt. induction H ; cbn.
- reflexivity.
- now rewrite H, IHForall.
Qed.
#[export] Hint Rewrite @substitute_substitute : subst.

Lemma scomp_assoc {s s' s'' s'''} (σ1 : subst s s') (σ2 : subst s' s'') (σ3 : subst s'' s''') :
  scomp (scomp σ1 σ2) σ3 = scomp σ1 (scomp σ2 σ3).
Proof. subst_ext i. simpl_subst. reflexivity. Qed.
#[export] Hint Rewrite @scomp_assoc : subst.

Lemma scomp_scons_l {x s s' s''} t (σ1 : subst s s') (σ2 : subst s' s'') :
  scomp (scons x t σ1) σ2 = scons x (substitute σ2 t) (scomp σ1 σ2).
Proof. subst_ext i. depelim i ; simpl_subst ; reflexivity. Qed.
#[export] Hint Rewrite @scomp_scons_l : subst.

Lemma scomp_sup_l {x s s' s''} (σ1 : subst s s') (σ2 : subst (s' ▷ x) s'') :
  scomp (sup x σ1) σ2 = scons x (sapply σ2 I0) (scomp (scomp σ1 sshift) σ2).
Proof. subst_ext i. depelim i ; simpl_subst ; reflexivity. Qed.
#[export] Hint Rewrite @scomp_sup_l : subst.

(***********************************************************************)
(** * Lemmas about [sren]. *)
(***********************************************************************)

Lemma sapply_sren {s s'} (ρ : ren s s') i :
  sapply (sren ρ) i = TVar (rapply ρ i).
Proof. reflexivity. Qed.
#[export] Hint Rewrite @sapply_sren : subst.

Lemma sren_rid {s} :
  sren (@rid s) = sid.
Proof. subst_ext i. reflexivity. Qed.
(* #[export] Hint Rewrite @sren_rid : subst.*)

Lemma sren_rshift {s x} :
  sren (@rshift s x) = sshift.
Proof. subst_ext i. reflexivity. Qed.
(* #[export] Hint Rewrite @sren_rshift : subst.*)

Lemma sren_rcons {s s' x} i (ρ : ren s s') :
  sren (rcons x i ρ) = scons x (TVar i) (sren ρ).
Proof. subst_ext j. depelim j ; simpl_subst ; reflexivity. Qed.
(* #[export] Hint Rewrite @sren_rcons : subst.*)

Lemma sren_rcomp {s s' s''} (ρ1 : ren s s') (ρ2 : ren s' s'') :
  sren (rcomp ρ1 ρ2) = scomp (sren ρ1) (sren ρ2).
Proof. subst_ext i. reflexivity. Qed.
(* #[export] Hint Rewrite @sren_rcomp : subst.*)

Lemma sren_rup {x s s'} (ρ : ren s s') :
  sren (rup x ρ) = sup x (sren ρ).
Proof. subst_ext i. depelim i ; simpl_subst ; reflexivity. Qed.
(* #[export] Hint Rewrite @sren_rup : subst.*)

Lemma substitute_sren {s s'} (ρ : ren s s') t :
  substitute (sren ρ) t = rename ρ t.
Proof.
induction t using term_ind' in s', ρ |- * ; simpl_subst.
- reflexivity.
- reflexivity.
- rewrite <-sren_rup. now rewrite IHt1, IHt2.
- rewrite <-sren_rup. now rewrite IHt1, IHt2.
- rewrite IHt. f_equal. induction H ; cbn.
  + reflexivity.
  + now rewrite H, IHForall.
- reflexivity.
Qed.
#[export] Hint Rewrite @substitute_sren : subst.

Lemma substitute_sshift {s x} t :
  substitute (@sshift s x) t = rename rshift t.
Proof. rewrite <-substitute_sren. reflexivity. Qed.
#[export] Hint Rewrite @substitute_sshift : subst.

(***********************************************************************)
(** * Substitutions and closed terms. *)
(***********************************************************************)

Lemma subst_closed {s} (σ : subst ∅ s) :
  σ = sren wk_idx.
Proof. subst_ext i. depelim i. Qed.

Lemma substitute_closed {s} (σ : subst ∅ s) (t : term ∅) :
  substitute σ t = wk t.
Proof. rewrite (subst_closed σ). simpl_subst. reflexivity. Qed.

Lemma substitute_wk_closed {s s'} (σ : subst s s') (t : term ∅) :
  substitute σ (wk t) = wk t.
Proof.
unfold wk. simpl_subst. rewrite (subst_closed (rscomp wk_idx σ)).
simpl_subst. reflexivity.
Qed.
#[export] Hint Rewrite @substitute_wk_closed : subst.

(** TODO: srcomp and rscomp when the left-hand side is [cons] or [up]. *)