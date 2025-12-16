From Equations Require Import Equations.

Inductive context (s : nat) : nat -> Type :=
| CNil : context s s
| CCons {s'} : context s s' -> context s (S s').

Derive Signature NoConfusion NoConfusionHom for context.
