From Metaprog Require Import Prelude MetaMonad.

(** The effect [failE] allows meta-programs to throw fatal errors. *)
Variant failE : Type -> Type :=
| Fail {A} (s : string) : failE A.

(** [fail msg] crashes the program with error message [msg]. *)
Definition fail {E A} `{failE -< E} (s : string) : meta E A :=
  trigger (Fail s).
