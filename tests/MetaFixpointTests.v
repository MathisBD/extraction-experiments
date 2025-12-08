From Metaprog Require Import Control.Meta Control.Effects.Rec.

Section Test.
Context (E : Type -> Type).
Context (E_sub : recE E -< E).

MetaFixpoint fib n m : meta E _ :=
  match n with
  | 0 => ret 0
  | 1 => ret 1
  | S (S n) =>
    let% x := fib n m in
    let% y := fib (S n) m in
    ret (m + x + y)
  end.

Print fib.

End Test.

Print fib.