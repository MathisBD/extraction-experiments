From Metaprog Require Import Prelude.
From Metaprog Require Export Control.Effects.Fail Logic.WP.

(** This module defines the specification of the [failE] effect. *)

(** Logical effect handler for [failE]. *)
Program Definition handle_failE : handler failE := {|
  handler_fun _ e :=
    match e with
    | Fail msg => fun Φ g => False
    end
|}.
Next Obligation. intros A []. firstorder. Qed.

Lemma wp_fail {E A} (h : handler E) `{subhandler _ _ handle_failE h} Φ g msg :
  wp h A (fail msg) Φ g <-> False.
Proof. unfold fail, trigger. rewrite wp_Vis, handle_inj. cbn. reflexivity. Qed.
#[export] Hint Rewrite @wp_fail : wp.