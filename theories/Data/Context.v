From Metaprog Require Import Prelude Data.Term.

(** This module defines contexts, *)

(** [context s s'] is a context embedding terms from the inner scope [s']
    into the outer scope [s]. *)
Inductive context (s : scope) : scope -> Type :=
| CNil : context s s
| CCons {s'} (ctx : context s s') (x : tag) (ty : term s') : context s (s' ▷ x).

Arguments CNil {s}.
Arguments CCons {s s'}.

(** Lookup the type of a variable in a full context. *)
Equations lookup_context {s} : index s -> context ∅ s -> term s :=
lookup_context I0 (CCons ctx x ty) := wk ty ;
lookup_context (IS i) (CCons ctx x ty) := wk (lookup_context i ctx).

Equations prod_context {s s'} : context s s' -> (list (index s') -> term s') -> term s :=
prod_context CNil body := body nil ;
prod_context (CCons ctx x ty) body :=
  prod_context ctx $ fun is =>
  TLam x ty (body (map IS is ++ [I0])).

Equations lambda_context {s s'} : context s s' -> (list (index s') -> term s') -> term s :=
lambda_context CNil body := body nil ;
lambda_context (CCons ctx x ty) body :=
  lambda_context ctx $ fun is =>
  TLam x ty (body (map IS is ++ [I0])).
