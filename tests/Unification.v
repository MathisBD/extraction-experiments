From Stdlib Require Strings.PrimString.
From Equations Require Import Equations.
From Metaprog Require Import Prelude Data Control Logic MetaTheory.

Import ListNotations.
Import PrimString.PStringNotations.
Open Scope pstring_scope.

(***********************************************************************)
(** * Utility functions and notations. *)
(***********************************************************************)

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
(** * Unification algorithm. *)
(***********************************************************************)

Section UnifAlgorithm.

Context {E : Type -> Type}.

Context {Hprint : printE -< E}.
Context {Hfail : failE -< E}.
Context {Hrec : recE E -< E}.
Context {Hevar : evarE -< E}.

Context {h : handler E}.
Context {Hprint' : subhandler handle_printE h}.
Context {Hfail' : subhandler handle_failE h}.
Context {Hrec' : subhandler (handle_recE h) h}.
Context {Hevar' : subhandler handle_evarE h}.

(** [whd_evars evm t] will check if [t] is a defined evar, and if yes replace
    it with its body. *)
MetaFixpoint whd_evars {s} (t : term s) : meta E (term s) :=
  match t with
  | TEvar ev =>
      let% def_opt := lookup_evar_def ev in
      match def_opt with
      | Some def => whd_evars (wk def)
      | None => ret (TEvar ev)
      end
  | _ => ret t
  end.

(** [allM pred xs] checks if [pred] is true on all elements of [xs]. *)
Fixpoint allM {E A} (pred : A -> meta E bool) (xs : list A) : meta E bool :=
  match xs with
  | [] => ret true
  | x :: xs => pred x and% allM pred xs
  end.

(** [allM2 pred xs ys] checks if [pred] is true on all elements of [xs] and [ys].
    Fails if [xs] and [ys] are not of the same length. *)
Fixpoint allM2 {E A1 A2} `{failE -< E} (pred : A1 -> A2 -> meta E bool) (xs : list A1) (ys : list A2) : meta E bool :=
  match xs, ys with
  | [], [] => ret true
  | x :: xs, y :: ys => pred x y and% allM2 pred xs ys
  | _, _ => fail "allM2: lengths don't match"
  end.

(** [mapM2 f xs] maps function [f] over the lists [xs] and [ys] and collects the results.
    Effects are sequenced from left to right.
    Fails if [xs] and [ys] are not the same length. *)
Fixpoint mapM2 {E A1 A2 B} `{failE -< E} (f : A1 -> A2 -> meta E B) (xs : list A1) (ys : list A2) : meta E (list B) :=
  match xs, ys with
  | [], [] => ret nil
  | x :: xs, y :: ys =>
    let% z := f x y in
    let% zs := mapM2 f xs ys in
    ret (z :: zs)
  | _, _ => fail "mapM2: lengths don't match"
  end.

MetaFixpoint eq_term_evars {s} (t u : term s) : meta E bool :=
  let% t := whd_evars t in
  let% u := whd_evars u in
  match t, u with
  | TType, TType => ret true
  | TVar x, TVar y => ret (index_eq x y)
  | TLam x ty body, TLam x' ty' body' =>
      eq_term_evars ty ty' and% eq_term_evars body (rename (replace_tag x) body')
  | TProd x a b, TLam x' a' b' =>
      eq_term_evars a a' and% eq_term_evars b (rename (replace_tag x) b')
  | TApp f args, TApp f' args' =>
    if Nat.eqb (List.length args) (List.length args')
    then eq_term_evars f f' and% allM2 eq_term_evars args args'
    else ret false
  | TEvar ev, TEvar ev' => ret (Nat.eqb ev ev')
  | _, _ => ret false
  end.

(***********************************************************************)
(** * Retyping. *)
(***********************************************************************)

(** Reduce a term to a product. Fails if the term is not a product. *)
Definition reduce_to_prod {s} : context ∅ s -> term s -> meta E { x & term s & term (s ▷ x) }.
Admitted.

Equations retype_spine {s} : context ∅ s -> term s -> list (term s) -> meta E (term s) :=
retype_spine Γ f_ty [] := ret f_ty ;
retype_spine Γ f_ty (arg :: args) :=
  let% ⟨x, a, b⟩ := reduce_to_prod Γ f_ty in
  retype_spine Γ (b[x := arg]) args.

(** [retype evm Γ t] computes the type of [t] in context [Γ] and evar-map [evm].
    Assumes [t] is already well-typed. *)
MetaFixpoint retype {s} (Γ : context ∅ s) (t : term s) : meta E (term s) :=
  match t with
  | TVar x => ret (lookup_context x Γ)
  | TType => ret TType
  | TLam x ty body =>
    let% body_ty := retype (CCons Γ x ty) body in
    ret (TProd x ty body_ty)
  | TProd x a b => ret TType
  | TEvar ev =>
    let% ev_type := lookup_evar_type ev in
    match ev_type with
    | Some ty => ret (wk ty)
    | None => fail "retype: unbound evar"
    end
  | TApp f args =>
    let% f_ty := retype Γ f in
    retype_spine Γ f_ty args
  end.

(***********************************************************************)
(** * Unification result. *)
(***********************************************************************)

(* TODO: seems fishy, we should probably reset the evar-map before [t2] somehow?
   This needs backtracking. *)
Definition or_backtrack (t1 t2 : meta E bool) : meta E bool :=
  let% b1 := t1 in
  if b1 then ret true else t2.

Notation "t1 '<|>' t2" := (or_backtrack t1 t2) (at level 30, right associativity).

(** [stack] represents a term by separating the head from the list of arguments (aka spine).
    This is done to have O(1) access to the head β-redex.

    A stack is _normalized_ if the head:
    - is not an application, and
    - is not a defined evar. *)
Definition stack (s : scope) : Type :=
  term s * list (term s).

(** Turn a stack into a term. *)
Definition zip {s} (t : stack s) : term s :=
  TApp (fst t) (snd t).

(** Normalize a stack. *)
MetaFixpoint norm_stack {s} (t : stack s) : meta E (stack s) :=
  match t with
  | (TEvar ev, args) =>
    let% ev_def := lookup_evar_def ev in
    match ev_def with
    | Some def => norm_stack (wk def, args)
    | None => ret (TEvar ev , args)
    end
  | (TApp f args, args') => norm_stack (f, args ++ args')
  | _ => ret t
  end.

Definition is_var {s} (t : term s) : meta E bool :=
  let% t := whd_evars t in
  match t with
  | TVar _ => ret true
  | _ => ret false
  end.

Definition well_typed Σ {s} (Γ : context ∅ s) (t : term s) : Prop :=
  exists T, Σ ;; Γ ⊢ t : T.

Lemma well_typed_zip_nil Σ {s} Γ (t : term s) :
  well_typed Σ Γ t ->
  well_typed Σ Γ (zip (t, [])).
Proof.
intros [T Ht]. exists T. unfold zip. cbn. apply typing_app with T.
- assumption.
- constructor.
Qed.

Lemma well_typed_extend_evm {Σ1 Σ2 s} {Γ : context ∅ s} {t} :
  Σ1 ⊑ Σ2 ->
  well_typed Σ1 Γ t ->
  well_typed Σ2 Γ t.
Proof.
intros HΣ (T & Ht). exists T. now apply (typing_extend_evm HΣ).
Qed.

(** We do open recursion: this section defines a function [unify_step] which does
    a single unification step. We tie the loop after this section by taking
    the fixpoint of [unify_step]. *)
Section UnifyStep.
  Context (unify_stack : forall {s}, context ∅ s -> stack s -> stack s -> meta E bool).
  Arguments unify_stack {s}.

  Hypothesis wp_unify_stack :
    forall Σ {s} Γ (t u : stack s),
      typing_evar_map Σ ->
      well_typed Σ Γ (zip t) ->
      well_typed Σ Γ (zip u) ->
      wp h _ (unify_stack Γ t u) (fun b Σ' =>
        if b then Σ ⊑ Σ' /\ typing_evar_map Σ' /\ Σ' ⊢ zip t ≡ zip u
        else Σ' = Σ) Σ.

  (** Simple wrapper around [unify_stack]. *)
  Definition unify {s} (Γ : context ∅ s) (t u : term s) : meta E bool :=
    unify_stack Γ (t, []) (u, []).

  Lemma wp_unify Σ {s} Γ (t u : term s) :
    typing_evar_map Σ ->
    well_typed Σ Γ t ->
    well_typed Σ Γ u ->
    wp h _ (unify Γ t u) (fun b Σ' =>
      if b then Σ ⊑ Σ' /\ typing_evar_map Σ' /\ Σ' ⊢ t ≡ u
      else Σ' = Σ) Σ.
  Proof.
  intros HΣ Ht Hu. pose proof (H := wp_unify_stack Σ Γ (t, []) (u, []) HΣ).
  forward H. { now apply well_typed_zip_nil. }
  forward H. { now apply well_typed_zip_nil. }
  unfold unify. revert H. apply wp_consequence.
  intros [] Σ' ; [|auto]. intros (H1 & H2 & H3) ; split3 ; [assumption.. |].
  unfold zip in H3. cbn in H3. rewrite !red1_empty_app in H3. exact H3.
  Qed.

  (** Unify a list of terms. *)
  Equations unify_list {s} : context ∅ s -> list (term s) -> list (term s) -> meta E bool :=
  unify_list Γ [] [] := ret true ;
  unify_list Γ (t :: ts) (u :: us) := unify Γ t u and% unify_list Γ ts us ;
  unify_list _ _ _ := fail "unify_list: lengths don't match".

  (* we need [and%] to reset the evar-map if the first arg succeeds and the
     second one fails. *)
  Lemma wp_andM :

  Lemma wp_unify_list Σ {s} (Γ : context ∅ s) ts us :
    typing_evar_map Σ ->
    Forall (well_typed Σ Γ) ts ->
    Forall (well_typed Σ Γ) us ->
    List.length ts = List.length us ->
    wp h _ (unify_list Γ ts us) (fun b Σ' =>
      if b then Σ ⊑ Σ' /\ typing_evar_map Σ' /\ All2 (conv red_flags_all Σ') ts us
      else Σ' = Σ) Σ.
  Proof.
  intros HΣ Hts Hus Hlen. funelim (unify_list Γ ts us).
  - rewrite wp_ret. split3 ; easy.
  - depelim Hlen.
  - depelim Hlen.
  - unfold andM, ifM. rewrite wp_Bind. depelim Hts. depelim Hus.
    eapply wp_consequence ; [| eapply wp_unify] ; auto.
    intros [] Σ'.
    + intros (Hincl & HΣ' & Hconv). eapply wp_consequence ; [| eapply H] ; auto.
      * intros [] Σ'' ; [|auto]. intros (Hincl' & HΣ'' & Hconv'). split3.
        --now rewrite Hincl, Hincl'.
        --assumption.
        --constructor ; [now apply (conv_extend_evm Hincl') | assumption].
        --intros ->. auto.
      * revert Hts. admit.
      * revert Hus. admit.
    + intros ->. rewrite wp_ret. reflexivity.

  (** Structurally unify the heads of two terms. *)
  Equations unify_same : forall {s}, context ∅ s -> term s -> term s -> meta E bool :=
  (* Rule TYPE-SAME. *)
  unify_same Γ TType TType := ret true ;
  (* Rule VAR-SAME. *)
  unify_same Γ (TVar x) (TVar y) := ret $ index_eq x y ;
  (* Rule LAM-SAME. *)
  unify_same Γ (TLam x ty body) (TLam y ty' body') :=
    unify Γ ty ty' and%
    unify (CCons Γ x ty) body (rename (replace_tag x) body') ;
  (* Rule PROD-SAME. *)
  unify_same Γ (TProd x a b) (TProd y a' b') :=
    unify Γ a a' and%
    unify (CCons Γ x a) b (rename (replace_tag x) b') ;
  unify_same Γ _ _ := ret false.

  (** Rule APP-FO. *)
  Equations unify_app_fo : forall {s}, context ∅ s -> stack s -> stack s -> meta E bool :=
  unify_app_fo Γ (f, args) (f', args') :=
    if Nat.eqb (List.length args) (List.length args')
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
  Definition decompose_prod {s} (t : term s) : { s' & context s s' & term s' }.
  Admitted.
  (*decompose_prod (TProd x ty body) :=
    let ⟨s', Γ', t'⟩ := decompose_prod body in
    ⟨s', ccons_left x ty Γ', t'⟩ ;
  decompose_prod t := ⟨s, CNil, t⟩.
  Next Obligation. simp term_size. lia. Qed.*)

  (** Technical detail: [prune_ctx] expects the list of booleans [pos] to be in reverse order
      (i.e. the left-most element in [pos] corresponds to the right-most element in [Γ]). *)
  Equations prune_ctx {s} : list bool -> context ∅ s -> meta E { s' & context ∅ s' & thinning s' s} :=
  prune_ctx (true :: bs) (CCons Γ x ty) :=
    let% ⟨s', Γ', δ⟩ := prune_ctx bs Γ in
    (* Check if [ty] uses only variables in [s']. *)
    match thin_inv δ ty with
    | Some ty' => ret ⟨s' ▷ x, CCons Γ' x ty', ThinKeep δ⟩
    | None => ret ⟨s', Γ', ThinSkip δ⟩
    end ;
  prune_ctx (false :: bs) (CCons Γ x ty) :=
    let% ⟨s', Γ', δ⟩ := prune_ctx bs Γ in
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
    let% ⟨s', Γ', δ⟩ := prune_ctx (rev pos) Γ in
    match thin_inv δ ty with
    | Some ty' => ret $ Some ⟨s', Γ', ty', δ⟩
    | None => ret None
    end.

  (** Rule META-SAME. *)
  Equations unify_meta_same {s} : context ∅ s -> stack s -> stack s -> meta E bool :=
  unify_meta_same Γ (TEvar ev, args) (TEvar ev', args') :=
    (* Check all the arguments are variables. *)
    if% ret (Nat.eqb ev ev') and% allM is_var args and% allM is_var args' then
      (* Compute the list of positions where the arguments agree (resp. don't agree). *)
      let% pos := mapM2 eq_term_evars args args' in
      (* Decompose the type of [ev]. *)
      let% ev_type := lookup_evar_type ev in
      let% ev_type :=
        match ev_type with
        | Some ty => ret ty
        | None => fail "unify_meta_same: undefined evar"
        end
      in
      let '⟨s1, Γev, Tev⟩ := decompose_prod ev_type in
      (* Prune the context [Γev] to obtain a smaller context [Γev'] and evar type [Γev' |- Tev']
         and a thinning [thin : ren s2 s1]. *)
      let% x := prune pos Γev Tev in
      match x with
      | None => ret false
      | Some ⟨s2, Γev', Tev', thin⟩ =>
        (* Create a new evar [new_ev : ∀ Γev', Tev']. *)
        let% new_ev := fresh_evar (prod_context Γev' $ fun _ => Tev') in
        (* Set [ev := λ (xs : Γev) => new_evar (filter_list pos xs)]. *)
        let ev_def := lambda_context Γev $ fun is =>
          TApp (TEvar ev) (filter_list pos $ map TVar is)
        in
        define_evar ev ev_def >>
        ret true
      end
    else ret false ;
  unify_meta_same _ _ _ := ret false.

  (** Get the index of a variable. Rets [None] if the term is not a variable. *)
  Definition dest_var {s} (t : term s) : meta E (option (index s)) :=
    let% t := whd_evars t in
    match t with
    | TVar i => ret (Some i)
    | _ => ret None
    end.

  (** Assumes the variables [ys] are distinct. *)
  Equations invert_index {s s'} : index s -> list (index s) -> list (index s') -> meta E (option (index s')) :=
  invert_index y0 (y :: ys) (x :: xs) :=
    if index_eq y0 y then
      (* We don't need to check that [y0] is not in [ys] because the variables [ys] are
         assumed to be distinct. *)
      ret (Some x)
    else
      invert_index y0 ys xs ;
  invert_index y0 [] [] := ret None ;
  invert_index _ _ _ := fail "invert_index: lengths don't match".

  MetaFixpoint invert_term {s s'} (t : term s) (ys : list (index s)) (xs : list (index s')) : meta E (option (term s')) :=
    let% t := whd_evars t in
    match t with
    | TType => ret $ Some TType
    | TVar y =>
        let% x_opt := invert_index y ys xs in
        match x_opt with
        | Some x => ret $ Some (TVar x)
        | None => ret None
        end
    | TLam x ty body =>
        let% ty' := invert_term ty ys xs in
        let% body' := invert_term body (map IS ys) xs in
        match ty', body' with
        | Some ty', Some body' => ret $ Some $ TLam x ty' (wk body')
        | _, _ => ret None
        end
    | TProd x ty body =>
        let% ty' := invert_term ty ys xs in
        let% body' := invert_term body (map IS ys) xs in
             match ty', body' with
        | Some ty', Some body' => ret $ Some $ TProd x ty' (wk body')
        | _, _ => ret None
        end
    | TApp f args =>
        let% f' := invert_term f ys xs in
        let% args' := mapM (fun arg => invert_term arg ys xs) args in
        match f', option_sequence args' with
        | Some f', Some args' => ret $ Some $ TApp f' args'
        | _, _ => ret None
        end
    | TEvar ev => ret $ Some $ TEvar ev
    end.

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

  (** Rets the indices in [Γ] as [n; ... 3; 2; 1; 0]. *)
  Definition context_indices {s s'} (Γ : context s s') : list (index s') :=
    rev (context_indices_aux Γ).

  Equations unify_meta_inst_l {s} : context ∅ s -> stack s -> stack s -> meta E bool :=
  unify_meta_inst_l Γ (TEvar ev, args) t :=
    (* Check the arguments are _distinct_ variables. *)
    match is_distinct_vars args with
    | Some vars =>
      (* Decompose the type of [ev]. *)
      let% ev_type := lookup_evar_type ev in
      let% ev_type :=
        match ev_type with
        | Some ty => ret ty
        | None => fail "unify_meta_inst_l: undefined evar"
        end
      in
      let '⟨s1, Γev, Tev⟩ := decompose_prod ev_type in
      (* Invert the right-hand-side [t]. *)
      let% t' : option (term s1) := invert_term (TApp (fst t) (snd t)) vars (context_indices Γev) in
      match t' with
      | None => ret false
      | Some t' =>
        (* Perform the occurs-check. *)
        if has_evar ev t' then ret false else
        (* Unify the type of [t'] and the type of [Tev]. *)
        let% t_ty' := retype Γev t' in
        unify Γev t_ty' Tev and%
        (* Define the evar. *)
        let ev_body := lambda_context Γev $ fun _ => t' in
        define_evar ev ev_body >>
        ret true
      end
    | None => ret false
    end ;
  unify_meta_inst_l _ _ _ := ret false.

  (** Apply a single rule, and recurse using [unify_stack]. *)
  Definition unify_step {s} (Γ : context ∅ s) (t u : stack s) : meta E bool :=
    let% t := norm_stack t in
    let% u := norm_stack u in
    (* First try to instantiate any evar. *)
    unify_meta_same Γ t u <|> unify_meta_inst_l Γ t u <|>
    (* Then try structural unification. *)
    unify_app_fo Γ t u <|>
    (* Finally try to use reduction rules. *)
    unify_beta_l Γ t u <|> unify_beta_r Γ t u.

End UnifyStep.

(** Main entry point of the unification algorithm. *)
MetaFixpoint unify_stack {s} : context ∅ s -> stack s -> stack s -> meta E bool :=
  unify_step (@unify_stack).

End UnifAlgorithm.