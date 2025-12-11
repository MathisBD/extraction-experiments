From Metaprog Require Import Prelude.
From Metaprog Require Export Data.Term.

(** [evar_entry] records the information pertaining to an evar: its type
    and optionally its definition. *)
Record evar_entry := mk_evar_entry {
  evar_type : term ∅ ;
  evar_def : option (term ∅)
}.

Derive NoConfusion NoConfusionHom for evar_entry.
