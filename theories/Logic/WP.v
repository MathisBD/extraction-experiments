From Metaprog Require Import Prelude.
From Metaprog Require Export Control.Meta MetaTheory.EvarMap Logic.Lattice.

(** This module defines the program logic. *)

(** [gstate] is the ghost state we use when verifying meta-programs
    using the program logic. *)
Definition gstate : Type := evar_map.

(***********************************************************************)
(** * Logical effect handlers. *)
(***********************************************************************)

(** A logical effect handler for effect [E] is a predicate
    transformer on events [e : E A], i.e. a function which maps postconditions
    [Φ : A -> gstate -> Prop] to preconditions [h e Φ : gstate -> Prop].

    Effect handlers are additionally required to be monotonic w.r.t. [Φ]
    i.e. to obey the consequence rule. *)
Record handler (E : Type -> Type) := mkhandler {
  (** The actual function of the handler. *)
  handler_fun A : E A -> (A -> gstate -> Prop) -> (gstate -> Prop) ;
  (** A proof of monotonicity. *)
  handler_mono A (e : E A) Φ Φ' g :
    (forall x g, Φ x g -> Φ' x g) ->
    handler_fun _ e Φ g ->
    handler_fun _ e Φ' g
}.

Arguments mkhandler {E}.
Arguments handler_fun {E} : simpl nomatch.
Arguments handler_mono {E}.

Coercion handler_fun : handler >-> Funclass.

(** We can freely change the postcondition of a handler to
    an equivalent one. *)
Lemma handler_equiv {E A} (h : handler E) (e : E A) Φ Φ' g :
  (forall x g, Φ x g <-> Φ' x g) ->
  h _ e Φ g <-> h _ e Φ' g.
Proof.
intros H. split ; intros H'.
- eapply handler_mono ; [|exact H']. firstorder.
- eapply handler_mono ; [|exact H']. firstorder.
Qed.

(** Handlers form a complete lattice. *)
Program Instance CompleteLattice_handler {E} : CompleteLattice (handler E) := {|
  leq h h' := leq (handler_fun h) (handler_fun h') ;
  weq h h' := weq (handler_fun h) (handler_fun h') ;
  isup I P f := {| handler_fun := isup P (fun i => handler_fun (f i)) |} ;
  iinf I P f := {| handler_fun := iinf P (fun i => handler_fun (f i)) |} ;
  cup h h' := {| handler_fun := cup (handler_fun h) (handler_fun h') |} ;
  cap h h' := {| handler_fun := cap (handler_fun h) (handler_fun h') |} ;
  bot := {| handler_fun := bot |} ;
  top := {| handler_fun := top |} ;
|}.
Next Obligation. intros. cbn in *. destruct H0. eexists ; eauto using handler_mono. Qed.
Next Obligation. intros. cbn in *. eauto using handler_mono. Qed.
Next Obligation. intros. cbn in *. destruct H0 ; [left | right] ; eauto using handler_mono. Qed.
Next Obligation. intros. cbn in *. destruct H0 ; split ; eauto using handler_mono. Qed.
Next Obligation. intros. cbn in *. firstorder. Qed.
Next Obligation. intros. cbn in *. firstorder. Qed.
Next Obligation.
intros E. split.
- intros h. reflexivity.
- intros h1 h2 h3 H1 H2. now transitivity h2.
Qed.
Next Obligation. intros E h h'. apply weq_spec. Qed.
Next Obligation. intros E I is hs h. apply leq_isup_x. Qed.
Next Obligation. intros E I is hs h. apply leq_x_iinf. Qed.
Next Obligation. intros E h1 h2 h3. apply leq_cup_x. Qed.
Next Obligation. intros E h1 h2 h3. apply leq_x_cap. Qed.
Next Obligation. intros E h. apply leq_x_top. Qed.
Next Obligation. intros E h. apply leq_bot_x. Qed.

(***********************************************************************)
(** * Sum of handlers. *)
(***********************************************************************)

(** [handler_sum h h'] is the disjoint sum of handlers [h] and [h']. *)
Program Definition handler_sum {E E'} (h : handler E) (h' : handler E') :
  handler (E +' E') :=
  {| handler_fun := fun A (e : (E +' E') A) =>
    match e with
    | sumE_l e => h _ e
    | sumE_r e => h' _ e
    end
  |}.
Next Obligation. destruct e ; eapply handler_mono ; eassumption. Qed.

(*Lemma handler_sum_mono {E1 E E'} (hh : handler E1 -> handler E S) (hh' : handler E1 S1 -> handler E' S) :
  monotone hh ->
  monotone hh' ->
  monotone (fun h => handler_sum (hh h) (hh' h)).
Proof.
intros H1 H2 h h' Hh. cbn in *. intros A [e | e] Φ s ; cbn.
- now apply H1.
- now apply H2.
Qed.*)

(***********************************************************************)
(** * Sub-handlers. *)
(***********************************************************************)

(** A handler [h : handler E] is a sub-handler of [h' : handler E'] iff:
    - [E] is included in [E'].
    - [h] and [h'] agree on every event [e : E].

    Typically, [h] and [h'] are subhandlers of [handler_sum h h'].
*)
Class subhandler {E E'} `{E -< E'} (h : handler E) (h' : handler E') := {
  handle_inj {A} (e : E A) (Φ : A -> gstate -> Prop) g :
    h' _ (inj_event e) Φ g <-> h _ e Φ g
}.

#[export] Instance subhandler_refl {E} (h : handler E) :
  subhandler h h.
Proof. constructor. reflexivity. Qed.

#[export] Instance subhandler_sum_l {E E1 E2 }
  (h : handler E) (h1 : handler E1) (h2 : handler E2) `{subhandler _ _ h h1} :
  subhandler h (handler_sum h1 h2).
Proof.
constructor. intros A e Φ g. cbn. rewrite handle_inj. reflexivity.
Qed.

#[export] Instance subhandler_sum_r {E E1 E2}
  (h : handler E) (h1 : handler E1) (h2 : handler E2) `{subhandler _ _ h h2} :
  subhandler h (handler_sum h1 h2).
Proof.
constructor. intros A e Φ g. cbn. rewrite handle_inj. reflexivity.
Qed.

(**************************************************************************)
(** * Weakest-precondition construction. *)
(**************************************************************************)

Section WP.
  Context {E : Type -> Type} (h : handler E).

  (** Weakest-precondition functor. *)
  Program Definition wp_step (R : handler (meta E)) : handler (meta E) := {|
    handler_fun _ m :=
      match m with
      | Ret x => fun Φ g => Φ x g
      | Bind m k => fun Φ g => R _ m (fun x g' => R _ (k x) Φ g') g
      | Vis e => fun Φ g => h _ e Φ g
      end
  |}.
  Next Obligation.
  intros R A m Φ Φ' g HΦ. destruct m.
  - firstorder.
  - apply handler_mono. intros x g'. apply handler_mono. firstorder.
  - apply handler_mono. firstorder.
  Qed.

  Lemma wp_step_mono : monotone wp_step.
  Proof.
  intros R R' HR A m Φ g. cbn. destruct m ; cbn.
  - firstorder.
  - intros H. cut (R _ m (fun x g' => R' _ (m0 x) Φ g') g).
    + apply HR.
    + revert H. apply handler_mono. intros x g'. apply HR.
  - firstorder.
  Qed.

  (** The weakest-precondition [wp] is constructed by taking the
      least fixpoint of [wp_step]. *)
  Definition wp : handler (meta E) := lfp wp_step.

End WP.

(* TODO: maybe use a better form of sealing. *)
Arguments wp : simpl never.

(**************************************************************************)
(** * Basic lemmas about WP. *)
(**************************************************************************)

Section BasicLemmas.
  Context {E : Type -> Type} {h : handler E}.

  (** Consequence rule. *)
  Lemma wp_consequence {A} {m : meta E A} {Φ Φ' g} :
    (forall x g, Φ x g -> Φ' x g) ->
    wp h _ m Φ g ->
    wp h _ m Φ' g.
  Proof. apply handler_mono. Qed.

  (** We can change the postcondition with an equivalent one. *)
  Lemma wp_equiv {A} (m : meta E A) {Φ Φ' g} :
    (forall x g, Φ x g <-> Φ' x g) ->
    wp h _ m Φ g <-> wp h _ m Φ' g.
  Proof. apply handler_equiv. Qed.

  (** Unfold a single step of [wp]. Consider using [wp_Ret], [wp_Bind],
      or [wp_Vis] instead. *)
  Lemma wp_unfold {A} {m : meta E A} {Φ g} :
    wp h _ m Φ g <-> wp_step h (wp h) _ m Φ g.
  Proof.
  pose proof (H := lfp_fixpoint (wp_step h) (wp_step_mono h)).
  specialize (H A m Φ g). cbn in H. rewrite H. reflexivity.
  Qed.

  Lemma wp_Ret {A} {x : A} {Φ g} :
    wp h _ (Ret x) Φ g <-> Φ x g.
  Proof. rewrite wp_unfold. reflexivity. Qed.

  Lemma wp_ret {A} (x : A) Φ g :
    wp h _ (ret x) Φ g <-> Φ x g.
  Proof. unfold ret. now rewrite wp_Ret. Qed.

  Lemma wp_Bind {A B} {m : meta E A} {f : A -> meta E B} {Φ g} :
    wp h _ (Bind m f) Φ g <-> wp h _ m (fun x g' => wp h _ (f x) Φ g') g.
  Proof. rewrite wp_unfold. reflexivity. Qed.

  Lemma wp_Vis {A} {e : E A} {Φ g} :
    wp h _ (Vis e) Φ g <-> h _ e Φ g.
  Proof. rewrite wp_unfold. reflexivity. Qed.

  Lemma wp_trigger {A E'} `{E' -< E} (e : E' A) Φ g :
    wp h _ (trigger e) Φ g <-> h _ (inj_event e) Φ g.
  Proof. unfold trigger. now rewrite wp_Vis. Qed.

End BasicLemmas.

(** [wp] is a monotone functon from effect handlers to effect handlers. *)
Lemma wp_mono {E} : monotone (@wp E).
Proof.
intros h1 h2 Hh. cbn in *. intros A m Φ g.
induction m in Φ, g |- *.
- rewrite !wp_Ret. firstorder.
- rewrite !wp_Bind. intros H1. cut (wp h1 _ m (fun x g' => wp h2 _ (m0 x) Φ g') g).
  + apply IHm.
  + revert H1. apply wp_consequence. intros x g'. apply H.
- rewrite !wp_Vis. apply Hh.
Qed.

(**************************************************************************)
(** * Induction and co-induction on WP. *)
(**************************************************************************)

(** We might wonder what happens if we define [wp] as a _greatest_
    fixpoint instead of a least fixpoint. Do we obtain a partial program logic?
    Remarkably, we obtain the same program logic: to control whether the logic
    is total/partial, we instead need to define the effect handler [h] as
    a least/greatest fixpoint.

    Thanks to this property we have both an induction and a coinduction
    principle for [wp].
*)

Section Induction.
  Context {E : Type -> Type} {h : handler E}.

  (** Induction principle on [wp], aka elimination principle. *)
  Lemma wp_ind (R : handler (meta E)) :
    (forall A a Φ g, Φ a g -> R A (Ret a) Φ g) ->
    (forall A B m k Φ g, R A m (fun x g' => R B (k x) Φ g') g -> R B (Bind m k) Φ g) ->
    (forall A e Φ g, h A e Φ g -> R A (Vis e) Φ g) ->
    forall A m Φ g, wp h A m Φ g -> R A m Φ g.
  Proof.
  intros Hret Hbind Hvis. apply (lfp_smallest (wp_step h) (wp_step_mono h)).
  cbn. intros A [a | m k | e] Φ g ; cbn.
  - apply Hret.
  - apply Hbind.
  - apply Hvis.
  Qed.

  (** Same as [wp] but as a _greatest_ fixpoint. *)
  Definition wp' (h : handler E) : handler (meta E) := gfp (wp_step h).

  Lemma wp_unfold' {A} {m : meta E A} {Φ g} :
    wp' h _ m Φ g <-> wp_step h (wp' h) _ m Φ g.
  Proof.
  pose proof (H := gfp_fixpoint (wp_step h) (wp_step_mono h)).
  specialize (H A m Φ g). cbn in H. rewrite H. reflexivity.
  Qed.

  (** The key property is that [wp'] admits the same induction (not coinduction)
      principle as [wp]. *)
  Lemma wp_ind' (R : handler (meta E)) :
    (forall A a Φ g, Φ a g -> R A (Ret a) Φ g) ->
    (forall A B m k Φ g, R A m (fun x g' => R B (k x) Φ g') g -> R B (Bind m k) Φ g) ->
    (forall A e Φ g, h A e Φ g -> R A (Vis e) Φ g) ->
    forall A m Φ g, wp' h A m Φ g -> R A m Φ g.
  Proof.
  intros Hret Hbind Hvis A m. induction m ; intros Φ g.
  - rewrite wp_unfold'. cbn. apply Hret.
  - rewrite wp_unfold'. cbn. intros H'. apply Hbind. apply IHm in H'. revert H'.
    apply handler_mono. intros x g'. apply H.
  - rewrite wp_unfold'. cbn. apply Hvis.
  Qed.

  Lemma wp_same_1 {A} (m : meta E A) Φ g :
    wp h _ m Φ g -> wp' h _ m Φ g.
  Proof.
  revert A m Φ g. apply wp_ind.
  - intros A a Φ g H. rewrite wp_unfold'. cbn. assumption.
  - intros A B m k Φ g H. rewrite wp_unfold'. cbn. assumption.
  - intros A e Φ g H. rewrite wp_unfold'. cbn. assumption.
  Qed.

  Lemma wp_same_2 {A} (m : meta E A) Φ g :
    wp' h _ m Φ g -> wp h _ m Φ g.
  Proof.
  revert A m Φ g. apply wp_ind'.
  - intros A a Φ g H. rewrite wp_Ret. assumption.
  - intros A B m k Φ g H. rewrite wp_Bind. assumption.
  - intros A e Φ g H. rewrite wp_Vis. assumption.
  Qed.

  (** This theorem justifies why we only use [wp] in the following,
      both when constructing a total and a partial program logic. *)
  Theorem wp_same {A} (m : meta E A) Φ g :
    wp h _ m Φ g <-> wp' h _ m Φ g.
  Proof. split ; [apply wp_same_1 | apply wp_same_2]. Qed.

  (** Co-induction principle on [wp], aka introduction principle. *)
  Lemma wp_coind (R : handler (meta E)) :
    (forall A a Φ g, R A (Ret a) Φ g -> Φ a g) ->
    (forall A B m k Φ g, R B (Bind m k) Φ g -> R A m (fun x g' => R B (k x) Φ g') g) ->
    (forall A e Φ g, R A (Vis e) Φ g -> h A e Φ g) ->
    forall A m Φ g, R A m Φ g -> wp h A m Φ g.
  Proof.
  intros Hret Hbind Hvis. setoid_rewrite wp_same.
  apply (gfp_greatest (wp_step h) (wp_step_mono h)). cbn.
  intros A [a | m k | e] Φ g ; cbn.
  - apply Hret.
  - apply Hbind.
  - apply Hvis.
  Qed.

End Induction.
