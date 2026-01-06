From Metaprog Require Import Prelude.
From Metaprog Require Export Control.Effects.Iter Logic.WP.

(** This module defines the specification of the [iterE] effect. *)

(** Logical effect handler for [iterE]. *)
Program Definition handle_iterE {E} `{iterE E -< E} (h : handler E) : handler (iterE E) := {|
  handler_fun _ e :=
    match e with
    | Iter a step => fun Φ g =>
      wp h _ (step a) (fun res g' =>
        match res with
        | Continue a' => wp h _ (iter a' step) Φ g'
        | Break b => Φ b g'
        end) g
    end
|}.
Next Obligation.
intros E HE h _ [A B body a] Φ Φ' g HΦ. apply wp_consequence.
intros [a' | b] g'.
- apply wp_consequence. firstorder.
- firstorder.
Qed.

Lemma handle_iterE_mono {E} `{iterE E -< E} : monotone (@handle_iterE E _).
Proof.
intros h h' Hh. cbn. unfold eq1. intros _ [A B body a] Φ g. cbn.
intros H1. eapply wp_mono ; [eassumption|]. revert H1. apply wp_consequence.
intros [a' | b] g'.
- now apply wp_mono.
- firstorder.
Qed.

Lemma wp_iter {E A B} `{iterE E -< E} {h : handler E} `{subhandler _ _ (handle_iterE h) h}
  (a : A) (step : A -> meta E (iter_step A B)) Φ g :
  wp h _ (iter a step) Φ g <->
  wp h _ (step a) (fun res g' =>
    match res with
    | Continue a' => wp h _ (iter a' step) Φ g'
    | Break b => Φ b g'
    end) g.
Proof.
unfold iter at 1. unfold trigger. rewrite wp_Vis, handle_inj. cbn.
(* The goal at this point is really weird: why is the left-hand-side a match which
   returns an equality? It's applied to eq_refl though so it doesn't matter. *)
apply wp_equiv. intros [a' | b] g' ; reflexivity.
Qed.
