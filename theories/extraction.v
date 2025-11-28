From Stdlib Require Import String Extraction.

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive nat => int [ "0" "succ" ]
   "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".
Extract Inductive list => "list" [ "[]" "(::)" ].

Inductive tag : Prop :=
| TAG.

Inductive scope : Prop :=
| SNil
| SCons (s : scope) (x : tag).

Notation "∅" := SNil.
Notation "s ▷ x" := (SCons s x) (at level 20, left associativity).

Inductive index : scope -> Type :=
| I0 {s x} : index (s ▷ x)
| IS {s x} : index s -> index (s ▷ x).

Extraction index.

(* We can extract indices to [int]. *)
Extract Inductive index => int [ "0" "succ" ]
   "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".

Definition evar_id := nat.

Inductive term : scope -> Type :=
| TType {s} : term s
| TVar {s} (i : index s) : term s
| TLam {s} (x : tag) (ty : term s) (body : term (s ▷ x)) : term s
| TProd {s} (x : tag) (a : term s) (b : term (s ▷ x)) : term s
| TApp {s} (f : term s) (args : list (term s)) : term s
| TEvar {s} (e : evar_id) : term s.

Extraction term.

Definition ren (s s' : scope) :=
  index s -> index s'.

Definition rid {s} : ren s s :=
  fun i => i.

Definition rshift {s α} : ren s (s ▷ α) :=
  fun i => IS i.

Definition rcomp {s1 s2 s3} (r1 : ren s1 s2) (r2 : ren s2 s3) : ren s1 s3 :=
  fun i => r2 (r1 i).

(* This is kind of funny: computationally it's the identity,
   but not in the types. *)
Definition replace_tag {s α} (β : tag) : ren (s ▷ α) (s ▷ β).
  destruct α ; destruct β ; exact rid.
Defined.

Print replace_tag.
Extraction replace_tag.

Inductive M : Type -> Type :=
| Ret {A} : A -> M A
| Bind {A B} : M A -> (A -> M B) -> M B
| Print : string -> M unit.

Extraction M.

Declare ML Module "extraction-experiments.plugin".

Definition test : nat := 3.

Set Extraction Output Directory "./theories".

Test M.
