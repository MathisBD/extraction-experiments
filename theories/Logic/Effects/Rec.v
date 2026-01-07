From Metaprog Require Import Prelude.
From Metaprog Require Export Control.Effects.Rec Logic.WP.

(** This module defines the specification of the [recE] effect. *)

Definition handle_recE {E} `{recE E -< E} (h : handler E) : handler (recE E).
Admitted.

Section WPs.
  Context {E : Type -> Type} {HE : recE E -< E}.
  Context {h : handler E} `{subhandler _ _ (handle_recE h) h}.
  Context {A : Type} {B : A -> Type}.

  Context (F : (forall a, meta E (B a)) -> (forall a, meta E (B a))).
  Context (P : A -> gstate -> Prop).
  Context (Q : forall a, B a -> gstate -> Prop).

  Hypothesis (HF : forall f,
      (forall a g, P a g -> wp h _ (f a) (Q a) g) ->
      (forall a g, P a g -> wp h _ (F f a) (Q a) g)).

  Lemma wp_fix1 a g :
    P a g -> wp h _ (fix1 F a) (Q a) g.
  Proof. Admitted.

End WPs.
