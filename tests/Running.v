From Stdlib Require Strings.PrimString.
From Metaprog.Control Require Import Meta Command Effects.All.
From Metaprog.Extraction Require Import All.

Import PrimString.PStringNotations.
Open Scope pstring_scope.

Definition prg : meta commandE unit :=
  (for% i = 1 to 10 do print "hello") >>
  print "done".

MetaFixpoint prg_rec i : meta commandE unit :=
  if Nat.ltb i 5 then print "hello" >> prg_rec (i + 1)
  else ret tt.

Definition test : unit := run_command (prg_rec 0).

Time Test test.