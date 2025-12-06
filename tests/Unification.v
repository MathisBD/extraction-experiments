From Stdlib Require Strings.PrimString.
From Stdlib Require Import Relations Morphisms Setoid Program Bool Nat List Lia.
From Equations Require Import Equations.
From Metaprog Require Import Term MetaMonad Effects.Print Effects.Fail Effects.Rec Effects.Evar.

Import ListNotations.
Import PrimString.PStringNotations.
Open Scope pstring_scope.

(***********************************************************************)
(** * Utility functions and notations. *)
(***********************************************************************)

(** Right-associative function application. *)
Notation "f $ x" := (f x) (at level 67, right associativity, only parsing).

Definition option_default {A} (a : A) (opt_a : option A) : A :=
  match opt_a with Some a => a | None => a end.

Definition option_apply {A B} (f : option (A -> B)) (x : option A) : option B :=
  match f, x with
  | Some f, Some x => Some (f x)
  | _, _ => None
  end.

Equations option_sequence {A} : list (option A) -> option (list A) :=
option_sequence nil := Some nil ;
option_sequence (None :: _) := None ;
option_sequence (Some x :: xs) := option_map (cons x) (option_sequence xs).

(** Map a function over two lists. *)
Equations map2 {A B C} : (A -> B -> C) -> list A -> list B -> list C :=
map2 f (x :: xs) (y :: ys) := f x y :: map2 f xs ys ;
map2 _ _ _ := [].

(** Zip two lists. *)
Definition zip {A B} (xs : list A) (ys : list B) : list (A * B) :=
  map2 pair xs ys.

(** [filter_list bs xs] filters the list [xs] by keeping only the elements
    for which the corresponding boolean in [bs] is [true].
    We assumes [bs] and [xs] have the same length. *)
Equations filter_list {A} : list bool -> list A -> list A :=
filter_list (true :: bs) (x :: xs) := x :: filter_list bs xs ;
filter_list (false :: bs) (x :: xs) := filter_list bs xs ;
filter_list _ _ := [].

Equations rev_acc {A} : list A -> list A -> list A :=
rev_acc acc [] := acc ;
rev_acc acc (x :: xs) := rev_acc (x :: acc) xs.

(** Tail recursive list reversal function (the one in the stdlib has quadratic complexity). *)
Definition rev {A} (xs : list A) : list A := rev_acc nil xs.

(***********************************************************************)
(** * Contexts. *)
(***********************************************************************)

Inductive context : scope -> scope -> Type :=
| CNil {s} : context s s
| CCons {s s'} (ctx : context s s') (x : tag) (ty : term s') : context s (s' ▷ x).

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

(***********************************************************************)
(** * Unification algorithm. *)
(***********************************************************************)

Section UnifAlgorithm.

Context {E : Type -> Type}.

Context {Hprint : printE -< E}.
Context {Hfail : failE -< E}.
Context {Hrec : recE E -< E}.
Context {Hevar : evarE -< E}.

(** [whd_evars evm t] will check if [t] is a defined evar, and if yes replace
    it with its body. *)
Definition whd_evars {s} (t : term s) : meta E (term s) :=
  letrec whd_evars s (t : term s) :=
    match t with
    | TEvar ev =>
        let* def_opt := lookup_evar_def ev in
        match def_opt with
        | Some def => whd_evars s (wk def)
        | None => ret $ TEvar ev
        end
    | _ => ret t
    end
  in
  whd_evars s t.

(** Check if two terms are equal modulo evar-expansion. This does not check for
    conversion modulo reduction rules (e.g. β-reduction). *)
Equations eq_term_evars_step : (forall s, term s -> term s -> meta E bool) ->
  (forall s, term s -> term s -> meta E bool) :=
eq_term_evars_step eq_term_evars s t u with whd_evars

Admitted.
(*  letrec eq_term_evars '(t, u) :=
    match t, u with
    | TType, TTYpe => ret true
    | _, _ => ret false
    end
  in
  eq_term_evars (t, u).

eq_term_evars evm t u with whd_evars evm t, whd_evars evm u := {
  | TType, TType => true
  | TVar x, TVar y => index_eq x y
  | TLam x ty body, TLam y ty' body' =>
      eq_term_evars evm ty ty' &&
      eq_term_evars evm body (rename (replace_tag x) body')
  | TProd x a b, TProd y a' b' =>
      eq_term_evars evm a a' &&
      eq_term_evars evm b (rename (replace_tag x) b')
  | TEvar ev, TEvar ev' => Nat.eqb ev ev'
  | _, _ => false
}.*)

(***********************************************************************)
(** * Retyping. *)
(***********************************************************************)

(** Reduce a term to a product. Fails if the term is not a product. *)
Definition reduce_to_prod {s} : context ∅ s -> term s -> meta E { x & term s & term (s ▷ x) }.
Admitted.

Equations retype_spine {s} : context ∅ s -> term s -> list (term s) -> meta E (term s) :=
retype_spine Γ f_ty [] := ret f_ty ;
retype_spine Γ f_ty (arg :: args) :=
  let* ⟨x, a, b⟩ := reduce_to_prod Γ f_ty in
  retype_spine Γ (b[x := arg]) args.

Equations retype_step (retype : {s & context ∅ s & term s } -> meta E (term s))

(** [retype evm Γ t] computes the type of [t] in context [Γ] and evar-map [evm].
    Assumes [t] is already well-typed. *)
Definition retype {s} (Γ : context ∅ s) (t : term s) : meta E (term s).
Admitted.
(*retype evm Γ (TVar x) := Some $ lookup_context x Γ ;
retype evm Γ TType := Some TType ;
retype evm Γ (TLam x ty body) :=
    match retype evm (CCons Γ x ty) body with
    | Some body_ty => Some $ TLam x ty body_ty
    | None => None
    end ;
retype evm Γ (TProd x a b) := Some TType ;
retype evm Γ (TEvar e) := option_map wk $ lookup_evar_type e evm ;
retype evm Γ (TApp f args) :=
    match retype evm Γ f with
    | Some f_ty => retype_spine Γ f_ty args
    | None => None
    end.
Next Obligation. simp term_size. lia. Qed.
Next Obligation. simp term_size. lia. Qed.*)

(***********************************************************************)
(** * Unification result. *)
(***********************************************************************)

Equations liftM {A} : option A -> meta E A :=
liftM (Some a) := ret a ;
liftM None := fail "liftM: got [None]".

(* TODO: seems fishy, we should probably reset the evar-map before [t2] somehow? *)
Definition orM (t1 t2 : meta E bool) : meta E bool :=
  let* b1 := t1 in
  if b1 then ret true else t2.

Notation "t1 '<|>' t2" := (orM t1 t2) (at level 30, right associativity).

Definition andM (t1 t2 : meta E bool) : meta E bool :=
  let* b1 := t1 in
  if b1 then t2 else ret false.

Notation "t1 '<&>' t2" := (andM t1 t2) (at level 30, right associativity).

(** [stack] represents a term by separating the head from the list of arguments (aka spine).
    This is done to have O(1) access to the head β-redex.

    A stack is _normalized_ if the head:
    - is not an application, and
    - is not a defined evar. *)
Definition stack (s : scope) : Type :=
  term s * list (term s).

(** Normalize a stack. *)
Definition norm_stack {s} (t : stack s) : meta E (stack s).
Admitted.
(*norm_stack evm (TApp f args, args') := norm_stack evm (f, args ++ args') ;
norm_stack evm (TEvar e, args) with lookup_evar_body e evm := {
  | Some body => norm_stack evm (wk body, args)
  | _ => (TEvar e, args)
} ;
norm_stack evm t := t.
Next Obligation. Admitted.
Next Obligation. Admitted.*)

Definition is_var {s} (t : term s) : meta E bool :=
  let* t := whd_evars t in
  match t with
  | TVar _ => ret true
  | _ => ret false
  end.

(** We do open recursion: this section defines a function [unify_step] which does
    a single unification step. We tie the loop after this section by taking
    the fixpoint of [unify_step]. *)
Section UnifyStep.
  Context (unify_stack : forall {s}, context ∅ s -> stack s -> stack s -> meta E bool).
  Arguments unify_stack {s}.

  (** Simple wrapper around [unify_stack]. *)
  Definition unify {s} (Γ : context ∅ s) (t u : term s) : meta E bool :=
    unify_stack Γ (t, []) (u, []).

  (** Unify a list of terms. *)
  Equations unify_list {s} : context ∅ s -> list (term s) -> list (term s) -> meta E bool :=
  unify_list Γ [] [] := ret true ;
  unify_list Γ (t :: ts) (u :: us) := unify Γ t u <&> unify_list Γ ts us ;
  unify_list _ _ _ := fail "unify_list: lengths don't match".

  (** Structurally unify the heads of two terms. *)
  Equations unify_same : forall {s}, context ∅ s -> term s -> term s -> meta E bool :=
  (* Rule TYPE-SAME. *)
  unify_same Γ TType TType := ret true ;
  (* Rule VAR-SAME. *)
  unify_same Γ (TVar x) (TVar y) := ret $ index_eq x y ;
  (* Rule LAM-SAME. *)
  unify_same Γ (TLam x ty body) (TLam y ty' body') :=
    unify Γ ty ty' <&>
    unify (CCons Γ x ty) body (rename (replace_tag x) body') ;
  (* Rule PROD-SAME. *)
  unify_same Γ (TProd x a b) (TProd y a' b') :=
    unify Γ a a' <&>
    unify (CCons Γ x a) b (rename (replace_tag x) b') ;
  unify_same Γ _ _ := ret false.

  (** Rule APP-FO. *)
  Equations unify_app_fo : forall {s}, context ∅ s -> stack s -> stack s -> meta E bool :=
  unify_app_fo Γ (f, args) (f', args') :=
    if Nat.eqb (length args) (length args')
    then unify_list Γ (f :: args) (f' :: args')
    else ret false.

  (** Rule BETA-LEFT. *)
  Equations unify_beta_l : forall {s}, context ∅ s -> stack s -> stack s -> meta E bool :=
  unify_beta_l Γ (TLam x ty body, arg :: args) u := unify_stack Γ (body[x := arg], args) u ;
  unify_beta_l _ _ _ := ret false.

  (** Rule BETA-RIGHT. *)
  Equations unify_beta_r : forall {s}, context ∅ s -> stack s -> stack s -> meta E bool :=
  unify_beta_r Γ t (TLam x ty body, arg :: args) := unify_stack Γ t (body[x := arg], args) ;
  unify_beta_r _ _ _ := ret false.

  Equations ccons_left {s s'} (x : tag) : term s -> context (s ▷ x) s' -> context s s' :=
  ccons_left x ty CNil := CCons CNil x ty ;
  ccons_left x ty (CCons Γ x' ty') := CCons (ccons_left x ty Γ) x' ty'.

  (* TODO: this should probably use reduction, and be a bit smarter to avoid using [ccons_left]
     which is very slow. *)
  Equations decompose_prod {s} (t : term s) : { s' & context s s' & term s' } by wf (term_size t) lt :=
  decompose_prod (TProd x ty body) :=
    let ⟨s', Γ', t'⟩ := decompose_prod body in
    ⟨s', ccons_left x ty Γ', t'⟩ ;
  decompose_prod t := ⟨s, CNil, t⟩.
  Next Obligation. simp term_size. lia. Qed.

  (** Technical detail: [prune_ctx] expects the list of booleans [pos] to be in reverse order
      (i.e. the left-most element in [pos] corresponds to the right-most element in [Γ]). *)
  Equations prune_ctx {s} : list bool -> context ∅ s -> meta E { s' & context ∅ s' & thinning s' s} :=
  prune_ctx (true :: bs) (CCons Γ x ty) :=
    let* ⟨s', Γ', δ⟩ := prune_ctx bs Γ in
    (* Check if [ty] uses only variables in [s']. *)
    match thin_inv δ ty with
    | Some ty' => ret ⟨s' ▷ x, CCons Γ' x ty', ThinKeep δ⟩
    | None => ret ⟨s', Γ', ThinSkip δ⟩
    end ;
  prune_ctx (false :: bs) (CCons Γ x ty) :=
    let* ⟨s', Γ', δ⟩ := prune_ctx bs Γ in
    ret ⟨s', Γ', ThinSkip δ⟩ ;
  prune_ctx nil CNil := ret ⟨∅, CNil, ThinNil⟩ ;
  prune_ctx _ _ := fail "prune_ctx: length of list and context don't match".

  (** [prune pos Γ ty] removes the types in [Γ] for which the corresponding element in [pos] is [false].
      It additionally removes all other types that depend on any of the removed variables,
      so that the resulting context is well-formed. Finally, we check that the type [ty] is well-scoped
      in the pruned context, and fail if it is not. [prune] additionally produces a thinning from
      the pruned context to the original context. *)
  Equations prune {s} : list bool -> context ∅ s -> term s -> meta E (option { s' & context ∅ s' & term s' & thinning s' s }) :=
  prune pos Γ ty :=
    let* ⟨s', Γ', δ⟩ := prune_ctx (rev pos) Γ in
    match thin_inv δ ty with
    | Some ty' => ret $ Some ⟨s', Γ', ty', δ⟩
    | None => ret None
    end.

  (** Rule META-SAME. *)
  Equations unify_meta_same {s} : context ∅ s -> stack s -> stack s -> meta E bool :=
  unify_meta_same Γ (TEvar ev, args) (TEvar ev', args') :=
    (* Check all the arguments are variables. *)
    if Nat.eqb ev ev' && forallb (is_var evm) args && forallb (is_var evm) args' then
      (* Compute the list of positions where the arguments agree (resp. don't agree). *)
      let pos := map2 (eq_term_evars evm) args args' in
      (* Decompose the type of [ev]. *)
      let* ev_type := liftM $ lookup_evar_type ev evm in
      let ⟨s1, Γev, Tev⟩ := decompose_prod ev_type in
      (* Prune the context [Γev] to obtain a smaller context [Γev'] and evar type [Γev' |- Tev']
         and a thinning [thin : ren s2 s1]. *)
      let* ⟨s2, Γev', Tev', thin⟩ := prune pos Γev Tev in
      (* Create a new evar [new_ev : ∀ Γev', Tev']. *)
      let (new_ev, evm) := fresh_evar evm (prod_context Γev' $ fun _ => Tev') in
      (* Set [ev := λ (xs : Γev) => new_evar (filter_list pos xs)]. *)
      let ev_body := lambda_context Γev $ fun is =>
        TApp (TEvar ev) (filter_list pos $ map TVar is)
      in
      let evm := define_evar evm ev ev_body in
      (* Finally return the updated evar-map. *)
      Yes evm
    else ret false ;
  unify_meta_same _ _ _ := ret false.

  (** Get the index of a variable. Returns [None] if the term is not a variable. *)
  Definition dest_var {s} (t : term s) : meta E (option (index s)) :=
    let* t := whd_evars evm t in
    match t with
    | TVar i => ret $ Some i
    | _ => ret None
    end.

  (** Assumes the variables [ys] are distinct. *)
  Equations invert_index {s s'} : index s -> list (index s) -> list (index s') -> meta E (index s') :=
  invert_index y0 (y :: ys) (x :: xs) :=
    if index_eq y0 y then
      (* We don't need to check that [y0] is not in [ys] because the variables [ys] are
         assumed to be distinct. *)
      ret x
    else
      invert_index y0 ys xs ;
  invert_index y0 [] [] := No ;
  invert_index _ _ _ := Error (* The lists should have the same length. *).

  Equations invert_term {s s'} (t : term s) (ys : list (index s)) (xs : list (index s')) :
    meta E (term s') by wf (term_size t) lt :=
  invert_term evm t ys xs with whd_evars evm t := {
    | TType => ret TType
    | TVar y => let* x := invert_index y ys xs in ret (TVar x)
    | TLam x ty body =>
        let* ty' := invert_term evm ty ys xs in
        let* body' := invert_term evm body (map IS ys) xs in
        ret $ TLam x ty' (wk body')
    | TProd x ty body =>
        let* ty' := invert_term evm ty ys xs in
        let* body' := invert_term evm body (map IS ys) xs in
        ret $ TProd x ty' (wk body')
    | TApp f args =>
        let* f' := invert_term evm f ys xs in
        let* args' := mapM (fun arg => invert_term evm arg ys xs) args in
        ret $ TApp f' args'
    | TEvar ev => ret $ TEvar ev
  }.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

  (** [has_evar ev t] returns [true] if [ev] occurs in the term [t]. *)
  Equations has_evar {s} : evar_id -> term s -> bool :=
  has_evar ev TType := false ;
  has_evar ev (TVar _) := false ;
  has_evar ev (TLam x ty body) := has_evar ev ty || has_evar ev body ;
  has_evar ev (TProd x a b) := has_evar ev a || has_evar ev b ;
  has_evar ev (TApp f args) := existsb (has_evar ev) (f :: args) ;
  has_evar ev (TEvar ev') := Nat.eqb ev ev'.

  (** [is_distinct_vars [t_0 ... t_n]] checks that each term [t_i] is a variable [TVar idx_i],
      and that all the indices [idx_i] are distinct. It returns the list [idx_0 ... idx_n],
      or [None] if the check failed. *)
  Definition is_distinct_vars {s} : list (term s) -> option (list (index s)).
  Admitted.

  (* TODO: this shouldn't be quadratic. *)
  Equations context_indices_aux {s s'} : context s s' -> list (index s') :=
  context_indices_aux CNil := [] ;
  context_indices_aux (CCons Γ _ _) := I0 :: map IS (context_indices_aux Γ).

  (** Returns the indices in [Γ] as [n; ... 3; 2; 1; 0]. *)
  Definition context_indices {s s'} (Γ : context s s') : list (index s') :=
    rev (context_indices_aux Γ).

  Equations unify_meta_inst_l {s} : context ∅ s -> stack s -> stack s -> meta E bool :=
  unify_meta_inst_l Γ evm (TEvar ev, args) t :=
    (* Check the arguments are _distinct_ variables. *)
    match is_distinct_vars args with
    | Some vars =>
      (* Decompose the type of [ev]. *)
      let* ev_type := liftM $ lookup_evar_type ev evm in
      let ⟨s1, Γev, Tev⟩ := decompose_prod ev_type in
      (* Invert the right-hand-side [t]. *)
      let* t' : term s1 := invert_term evm (TApp (fst t) (snd t)) vars (context_indices Γev) in
      (* Perform the occurs-check. *)
      let* () := if has_evar ev t' then No else Yes () in
      (* Unify the type of [t'] and the type of [Tev]. *)
      let* t_ty' := liftM $ retype evm Γev t' in
      let* evm := unify Γev evm t_ty' Tev in
      (* Define the evar. *)
      let ev_body := lambda_context Γev $ fun _ => t' in
      let evm := define_evar evm ev ev_body in
      (* Finally return the updated evar-map. *)
      Yes evm
    | None => No
    end ;
  unify_meta_inst_l _ _ _ _ := No.

  (** Apply a single rule, and recurse using [unify_stack]. *)
  Definition unify_step {s} (Γ : context ∅ s) (t u : stack s) : meta E bool :=
    let t := norm_stack evm t in
    let u := norm_stack evm u in
    (* First try to instantiate any evar. *)
    unify_meta_same Γ evm t u <|> unify_meta_inst_l Γ evm t u <|>
    (* Then try structural unification. *)
    unify_app_fo Γ evm t u <|>
    (* Finally try to use reduction rules. *)
    unify_beta_l Γ evm t u <|> unify_beta_r Γ evm t u.

End UnifyStep.

(** Main entry point of the unification algorithm. *)
Equations unify_stack {s} (Γ : context ∅ s) (t u : stack s) : meta E bool :=
unify_stack Γ evm t u := unify_step (fun _ Γ evm t u => unify_stack Γ evm t u) Γ evm t u.
Next Obligation. Admitted.