From Stdlib Require Strings.PrimString.
From Metaprog Require Import Control.Command Extraction.All.

Import PrimString.PStringNotations.
Open Scope pstring_scope.

Definition prg : meta commandE unit :=
  (for% i = 1 to 10 do print "hello") >>
  print "done".

MetaFixpoint prg_rec i : meta commandE unit :=
  if Nat.ltb i 5 then print "hello" >> prg_rec (i + 1)
  else ret tt.

Definition term_of {s} (x : tag) `{ScopeMem x s} : term s :=
  TVar (idx_of x).

Definition test_evar : meta commandE unit :=
  let ty : term ∅ :=
    prod TType (fun a =>
      arrow (term_of a) (arrow (term_of a) (term_of a))) in
  let% ev := fresh_evar ty in
  print "done".

Definition test : unit := run_command (test_evar).

Time Test test.
Test test.