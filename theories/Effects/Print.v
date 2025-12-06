From Metaprog Require Import Prelude MetaMonad.

(** The effect [printE] allows meta-programs to use logging facilities. *)
Variant printE : Type -> Type :=
| Print (s : string) : printE unit.

(** [print msg] prints the string [msg]. A newline is automatically inserted
    at the end of the string. *)
Definition print {E} `{printE -< E} (s : string) : meta E unit :=
  trigger (Print s).
