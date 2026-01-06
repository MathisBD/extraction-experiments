From Metaprog Require Import Prelude.
From Metaprog Require Export Control.Effects.Print Logic.WP.

(** This module defines the specification of the [printE] effect. *)

(** Logical effect handler for [printE]. *)
Program Definition handle_printE : handler printE := {|
  handler_fun _ e :=
    match e with
    | Print msg => fun Φ g => Φ tt g
    end
|}.
Next Obligation. intros A [msg] Φ Φ' g HΦ. firstorder. Qed.

Lemma wp_print {E} (h : handler E) `{subhandler _ _ handle_printE h} Φ g msg :
  wp h _ (print msg) Φ g <-> Φ tt g.
Proof.
unfold print, trigger. rewrite wp_Vis, handle_inj. cbn. reflexivity.
Qed.
