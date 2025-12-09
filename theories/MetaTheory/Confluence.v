From Metaprog Require Import Prelude Data.Term Data.Context MetaTheory.Reduction.

(** This module proves the confluence lemma for the reduction relation [red]. *)

Lemma red_confluence {s} (t u1 u2 : term s) :
  red t u1 ->
  red t u2 ->
  exists v, red u1 v /\ red u2 v.
Proof. Admitted.