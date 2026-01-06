From Metaprog Require Import Prelude.
From Metaprog Require Export Control.Meta.
From Metaprog.Control.Effects Require Export Print Fail Iter Rec Evar.

(** This module defines the aggregate effect [commandE] used when running commands. *)

Inductive commandE (A : Type) : Type :=
| command_print (e : printE A)
| command_fail (e : failE A)
| command_iter (e : iterE commandE A)
| command_rec (e : recE commandE A)
| command_evar (e : evarE A).

Arguments command_print {A}.
Arguments command_fail {A}.
Arguments command_iter {A}.
Arguments command_rec {A}.
Arguments command_evar {A}.

#[export] Instance subeffect_printE_commandE : printE -< commandE := {
  inj_event := @command_print
}.

#[export] Instance subeffect_failE_commandE : failE -< commandE := {
  inj_event := @command_fail
}.

#[export] Instance subeffect_iterE_commandE : iterE commandE -< commandE := {
  inj_event := @command_iter
}.

#[export] Instance subeffect_recE_commandE : recE commandE -< commandE := {
  inj_event := @command_rec
}.

#[export] Instance subeffect_evarE_commandE : evarE -< commandE := {
  inj_event := @command_evar
}.
