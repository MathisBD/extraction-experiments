Declare ML Module "extraction-experiments.plugin".

MetaFixpoint fib {k : bool} n :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S n) => fib n + fib (S n)
  end.