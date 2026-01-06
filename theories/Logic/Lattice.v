From Metaprog Require Import Prelude.

(** This module defines the class [CompleteLattice X] of complete lattices
    over a type [X].

    We prove basic properties, most notably the existence of least/greatest
    fixpoints of monotonous functions.
*)

(***********************************************************************)
(** * Complete lattice class. *)
(***********************************************************************)

(** A complete lattice over a type [X] is a partial order on [X] with
    arbitrary (i.e. infinitary) least upper bounds & greatest lower bounds.

    The typeclass includes many operations which can be derived from others
    (e.g. [cup] can be derived from [sup]): including all operations allows them
    to be mapped to the natural operations in the various instances.
*)
Class CompleteLattice (X : Type) := {
  (** [leq] is the partial order relation on [X]. *)
  leq : relation X ;
  (** [weq] is the symmetric closure of [leq]. Note that [leq] is usually not
      anti-symmetric, so [weq] is _not_ the default equality! *)
  weq : relation X ;
  (** [isup is xs] takes the least upper bound of an [I]-indexed family [xs]
      over a set of indices [is]. In math notation:
        [isup is xs = sup_(i ∈ is) xs_i]
  *)
  isup {I : Type} (is : I -> Prop) (xs : I -> X) : X ;
  (** [iinf is xs] takes the greatest lower bound of an [I]-indexed family [xs]
      over a set of indices [is]. In math notation:
        [iinf is xs = inf_(i ∈ is) xs_i]
  *)
  iinf {I : Type} (is : I -> Prop) (xs : I -> X) : X ;
  (** [cup x y] is the least upper bound of [x] and [y]. *)
  cup : X -> X -> X ;
  (** [cap x y] is the greatest lower bound of [x] and [y]. *)
  cap : X -> X -> X ;
  (** [top] is the greatest element in the lattice. *)
  top : X ;
  (** [bot] is the least element in the lattice. *)
  bot : X ;
  (** [leq] is a partial order. *)
  leq_PreOrder : PreOrder leq ;
  (** Specification of [weq]. *)
  weq_spec x y : weq x y <-> (leq x y /\ leq y x) ;
  (** Specification of [sup]. *)
  leq_isup_x I is xs y :
    leq (@isup I is xs) y <-> forall i, is i -> leq (xs i) y ;
  (** Specification of [inf]. *)
  leq_x_iinf I (is : I -> Prop) xs y :
    leq y (@iinf I is xs) <-> forall i, is i -> leq y (xs i) ;
  (** Specification of [cup]. *)
  leq_cup_x x y z : leq (cup x y) z <-> (leq x z /\ leq y z) ;
  (** Specification of [cap]. *)
  leq_x_cap x y z : leq z (cap x y) <-> (leq z x /\ leq z y) ;
  (** Specification of [top]. *)
  leq_x_top x : leq x top ;
  (** Specification of [bot]. *)
  leq_bot_x x : leq bot x ;
}.

Arguments weq {X _}.
Arguments leq {X _}.
Arguments isup {X _ I}.
Arguments iinf {X _ I}.
Arguments cup {X _}.
Arguments cap {X _}.
Arguments top {X _}.
Arguments bot {X _}.

#[export] Hint Mode CompleteLattice ! : typeclass_instances.

(** Complete lattices are a particular kind of preorders. *)
#[export] Existing Instance leq_PreOrder.

(** Notation for lattices which is only used in this file. *)
#[local] Declare Scope lattice.
#[local] Open Scope lattice.
#[local] Infix "==" := weq (at level 70) : lattice.
#[local] Infix "<=" := leq : lattice.

(***********************************************************************)
(** * Instances of complete lattices. *)
(***********************************************************************)

(** The canonical example of a complete lattice that we will use is the
    (dependent) function space [X := A1 -> A2 -> ... -> Prop] where the
    [Ai] are arbitrary types.
*)

(** Prop is a complete lattice. *)
#[export] Program Instance Prop_CompleteLattice : CompleteLattice Prop := {|
  leq p p' := p -> p' ;
  weq p p' := p <-> p' ;
  isup I is ps := exists2 i, is i & ps i;
  iinf I is ps := forall i, is i -> ps i;
  cup := or;
  cap := and;
  bot := False;
  top := True
|}.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.

(** [eq1 R f g] means that the (dependent) functions [f] and [g] are pointwise related by [R]. *)
Definition eq1 {A} {B : A -> Type} (R : forall a, relation (B a)) : relation (forall a, B a) :=
  fun f g => forall a, R a (f a) (g a).

(** (Dependent) functions into a complete lattice form a complete lattice. *)
#[export] Program Instance fun_CompleteLattice A (B : A -> Type)
  (LB : forall a, CompleteLattice (B a)) : CompleteLattice (forall a, B a) := {|
  leq := eq1 (fun a => leq (X := B a)) ;
  weq := eq1 (fun a => weq (X := B a)) ;
  isup I is fs := fun a => isup (X := B a) is (fun i => fs i a);
  iinf I is fs := fun a => iinf (X := B a) is (fun i => fs i a);
  cup f g := fun a => cup (X := B a) (f a) (g a);
  cap f g := fun a => cap (X := B a) (f a) (g a);
  bot := fun a => bot (X := B a);
  top := fun a => top (X := B a)
|}.
Next Obligation.
split.
- intros f a. reflexivity.
- intros f g h H1 H2 a. transitivity (g a) ; [apply H1 | apply H2].
Qed.
Next Obligation. unfold eq1. setoid_rewrite weq_spec. firstorder. Qed.
Next Obligation. unfold eq1. setoid_rewrite leq_isup_x. firstorder. Qed.
Next Obligation. unfold eq1. setoid_rewrite leq_x_iinf. firstorder. Qed.
Next Obligation. unfold eq1. setoid_rewrite leq_cup_x. firstorder. Qed.
Next Obligation. unfold eq1. setoid_rewrite leq_x_cap. firstorder. Qed.
Next Obligation. unfold eq1. apply leq_x_top. Qed.
Next Obligation. unfold eq1. apply leq_bot_x. Qed.

(***********************************************************************)
(** * Basic opeartions and properties. *)
(***********************************************************************)

Section Basics.
  Context {X : Type} {LX : CompleteLattice X}.

  (** Non-indexed version of [isup]. *)
  Definition sup (xs : X -> Prop) : X := isup (I := X) xs id.

  (** Non-indexed version of [iinf]. *)
  Definition inf (xs : X -> Prop) : X := iinf (I := X) xs id.

  Lemma leq_top_x (x : X) :
    top <= x <-> top == x.
  Proof.
  split ; intros H.
  - rewrite weq_spec. split ; [assumption | apply leq_x_top].
  - rewrite weq_spec in H. apply H.
  Qed.

  Lemma leq_x_bot (x : X) :
    x <= bot <-> x == bot.
  Proof.
  split ; intros H.
  - rewrite weq_spec. split ; [assumption | apply leq_bot_x].
  - rewrite weq_spec in H. apply H.
  Qed.

  Lemma leq_x_isup I (is : I -> Prop) (xs : I -> X) i :
    is i -> xs i <= isup is xs.
  Proof.
  intros Hi. pose proof (H := leq_isup_x I is xs (isup is xs)).
  now apply H in Hi.
  Qed.

  Lemma leq_iinf_x I (is : I -> Prop) (xs : I -> X) i :
    is i -> iinf is xs <= xs i.
  Proof.
  intros Hi. pose proof (H := leq_x_iinf I is xs (iinf is xs)).
  now apply H in Hi.
  Qed.

  Lemma leq_x_sup (xs : X -> Prop) x :
    xs x -> x <= sup xs.
  Proof. intros H. apply leq_x_isup with (xs := id) in H. apply H. Qed.

  Lemma leq_inf_x (xs : X -> Prop) x :
    xs x -> inf xs <= x.
  Proof. intros H. apply leq_iinf_x with (xs := id) in H. apply H. Qed.

  Lemma leq_sup_x (xs : X -> Prop) y :
    sup xs <= y <-> forall x, xs x -> x <= y.
  Proof. unfold sup. rewrite leq_isup_x. reflexivity. Qed.

  Lemma leq_x_inf (xs : X -> Prop) y :
    y <= inf xs <-> forall x, xs x -> y <= x.
  Proof. unfold inf. rewrite leq_x_iinf. reflexivity. Qed.

End Basics.

(**************************************************************************)
(** *** Least fixpoint construction. *)
(**************************************************************************)

Section LeastFixpoint.
  Context {X : Type} {L : CompleteLattice X} (F : X -> X).
  Hypothesis (Hmono : Proper (leq ==> leq) F).

  (** The set of (transfinite) iterations of [F]. *)
  Inductive lfp_chain : X -> Prop :=
  | lfp_chain_suc x : lfp_chain x -> lfp_chain (F x)
  | lfp_chain_sup : forall xs, xs <= lfp_chain -> lfp_chain (sup xs).

  (** The least fixpoint is the greatest element of the chain. *)
  Definition lfp : X := sup lfp_chain.

  (** [lfp] is a pre-fixpoint. *)
  Lemma lfp_prefixpoint : F lfp <= lfp.
  Proof.
  unfold lfp. apply leq_x_sup. apply lfp_chain_suc, lfp_chain_sup. reflexivity.
  Qed.

  Lemma lfp_chain_lfp : lfp_chain lfp.
  Proof. apply lfp_chain_sup. reflexivity. Qed.

  (** Elements of the chain are post-fixpoints. *)
  Lemma lfp_chain_postfixpoint x : lfp_chain x -> x <= F x.
  Proof.
  intros Hx. induction Hx.
  - now apply Hmono.
  - rewrite leq_sup_x. intros x Hx. rewrite H0 by assumption.
    apply Hmono. now apply leq_x_sup.
  Qed.

  (** [lfp] is indeed a fixpoint. *)
  Theorem lfp_fixpoint : F lfp == lfp.
  Proof.
  rewrite weq_spec. split.
  - apply lfp_prefixpoint.
  - apply lfp_chain_postfixpoint. apply lfp_chain_lfp.
  Qed.

  (** [lfp] is also the smallest (pre)fixpoint. *)
  Theorem lfp_smallest x : F x <= x -> lfp <= x.
  Proof.
  intro H. unfold lfp. rewrite leq_sup_x. intros y Hy.
  induction Hy.
  - rewrite <-H. now apply Hmono.
  - unfold id. rewrite leq_sup_x. assumption.
  Qed.

End LeastFixpoint.

(**************************************************************************)
(** *** Greatest fixpoint construction. *)
(**************************************************************************)

Section GreatestFixpoint.
  Context {X : Type} {L : CompleteLattice X} (F : X -> X).
  Hypothesis (Hmono : Proper (leq ==> leq) F).

  (** The set of (transfinite) iterations of [F]. *)
  Inductive gfp_chain : X -> Prop :=
  | gfp_chain_suc x : gfp_chain x -> gfp_chain (F x)
  | gfp_chain_inf : forall xs, xs <= gfp_chain -> gfp_chain (inf xs).

  (** The greatest fixpoint is the least element of the chain. *)
  Definition gfp := inf gfp_chain.

  Lemma gfp_chain_gfp : gfp_chain gfp.
  Proof. apply gfp_chain_inf. reflexivity. Qed.

  (** [gfp] is a post-fixpoint. *)
  Lemma gfp_postfixpoint : gfp <= F gfp.
  Proof.
  unfold gfp. apply leq_inf_x. apply gfp_chain_suc, gfp_chain_inf. reflexivity.
  Qed.

  (** Elements of the chain are pre-fixpoints. *)
  Lemma gfp_chain_prefixpoint x : gfp_chain x -> F x <= x.
  Proof.
  intros Hx. induction Hx.
  - now apply Hmono.
  - rewrite leq_x_inf. intros x Hs. transitivity (F x) ; [|now apply H0].
    apply Hmono. now apply leq_inf_x.
  Qed.

  (** [gfp] is indeed a fixpoint. *)
  Theorem gfp_fixpoint : F gfp == gfp.
  Proof.
  rewrite weq_spec. split.
  - apply gfp_chain_prefixpoint. apply gfp_chain_gfp.
  - apply gfp_postfixpoint.
  Qed.

  (** [gfp] is also the greatest (post)fixpoint. *)
  Theorem gfp_greatest x : x <= F x -> x <= gfp.
  Proof.
  intro H. unfold gfp. rewrite leq_x_inf. intros y Hy.
  induction Hy.
  - rewrite H. now apply Hmono.
  - rewrite leq_x_inf. assumption.
  Qed.

End GreatestFixpoint.