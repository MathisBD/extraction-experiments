(** This module lists the basic axioms we use. Indeed we don't try to keep
    the formalization axiom-free. We also don't go directly to full classical
    logic, but try to only use axioms which really make our like easier. *)

(** Functional extensionality: two dependent functions
    are equal if they are pointwise equal. *)
Axiom functional_extensionality :
  forall (A : Type) (B : A -> Type) (f g : forall a : A, B a),
  (forall a, f a = g a) ->
  f = g.

(** The tactic [fun_ext x1 x2 ... xn] applies the functional extentionality
    axiom [n] times and introduces variables [x1] to [xn]. *)

Tactic Notation "fun_ext" ident(x1) :=
  apply functional_extensionality ; intro x1.

Tactic Notation "fun_ext" ident(x1) ident(x2) :=
  apply functional_extensionality ; intro x1 ;
  apply functional_extensionality ; intro x2.

Tactic Notation "fun_ext" ident(x1) ident(x2) ident(x3) :=
  apply functional_extensionality ; intro x1 ;
  apply functional_extensionality ; intro x2 ;
  apply functional_extensionality ; intro x3.

Tactic Notation "fun_ext" ident(x1) ident(x2) ident(x3) ident(x4) :=
  apply functional_extensionality ; intro x1 ;
  apply functional_extensionality ; intro x2 ;
  apply functional_extensionality ; intro x3 ;
  apply functional_extensionality ; intro x4.

Tactic Notation "fun_ext" ident(x1) ident(x2) ident(x3) ident(x4) ident(x5) :=
  apply functional_extensionality ; intro x1 ;
  apply functional_extensionality ; intro x2 ;
  apply functional_extensionality ; intro x3 ;
  apply functional_extensionality ; intro x4 ;
  apply functional_extensionality ; intro x5.
