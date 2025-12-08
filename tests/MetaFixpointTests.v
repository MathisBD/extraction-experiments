Declare ML Module "extraction-experiments.plugin".

From Metaprog Require Import Control.Meta Control.Effects.Rec.

Register fix1 as metaprog.control.effects.rec.fix1.
Register fix2 as metaprog.control.effects.rec.fix2.
Register fix3 as metaprog.control.effects.rec.fix3.
Register fix4 as metaprog.control.effects.rec.fix4.
Register fix5 as metaprog.control.effects.rec.fix5.

Axiom (E : Type -> Type).
Instance E_sub : recE E -< E. Admitted.

Set Printing All.

Register E_sub as metaprog.e_sub.

MetaFixpoint test x1 x2 x3 x4 x5 x6 : meta E nat :=
  ret (x1 + 1).

MetaFixpoint fib n : meta E nat :=
  match n with
  | 0 => ret 0
  | 1 => ret 1
  | S (S n) =>
    let% x := fib n in
    let% y := fib (S n) in
    ret (x + y)
  end.

Check (fix1 (fun (fib : nat -> meta E nat) (n : nat) =>
 match n with
 | 0 => ret 0
 | 1 => ret 1
 | S (S n1) => let% x := fib n1 in (let% y := fib (S n1) in ret (x + y))
 end)).