From Metaprog Require Import Prelude.

(** This module defines _reduction flags_ which control which rules
    are allowed in the various reduction & conversion relations
    (e.g. [red] and [conv]).
*)

(***********************************************************************)
(** * Reduction flags. *)
(***********************************************************************)

(** Reduction flags [red_flags] control which rules are allowed in reduction:
    - [beta] controls beta reduction (function application).
    - [evars] controls evar expansion. *)
Record red_flags := {
  beta : bool ;
  evars : bool
}.

(** All reduction rules enabled. *)
Definition red_flags_all : red_flags :=
  {| beta := true ; evars := true |}.

(** All reduction rules disabled. *)
Definition red_flags_none : red_flags :=
  {| beta := false ; evars := false |}.

(** Only evar expansion is enabled. *)
Definition red_flags_evars : red_flags :=
  {| beta := false ; evars := true |}.

(***********************************************************************)
(** * Inclusion on reduction flags. *)
(***********************************************************************)

Record red_flags_incl (f1 f2 : red_flags) : Prop := {
  red_flags_incl_beta : f1.(beta) = true -> f2.(beta) = true ;
  red_flags_incl_evars : f1.(evars) = true -> f2.(evars) = true
}.

#[export] Instance red_flags_incl_Reflexive : Reflexive red_flags_incl.
Proof. intros f. constructor ; auto. Qed.

#[export] Instance red_flags_incl_Transitive : Transitive red_flags_incl.
Proof.
intros f1 f2 f3 H1 H2. constructor ; intros H ; now apply H1, H2 in H.
Qed.

Lemma red_flags_incl_none_l f :
  red_flags_incl red_flags_none f.
Proof. constructor ; cbn ; intros H ; depelim H. Qed.

Lemma red_flags_incl_all_r f :
  red_flags_incl f red_flags_all.
Proof. constructor ; cbn ; auto. Qed.
