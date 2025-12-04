From Metaprog Require Export Prelude.

(***********************************************************************)
(** * Scopes and de Bruijn indices. *)
(***********************************************************************)

(** We put tags in [Prop] so that they are erased by extraction.
    In the future we should put [tag] and [scope] in [Ghost]
    so that both get erased by extraction. *)
Inductive tag : Prop :=
| TAG.

Inductive scope : Set :=
| SNil
| SCons (s : scope) (x : tag).

Derive NoConfusion for scope.

(** [∅] is the empty scope: it contains no variables. *)
Notation "∅" := SNil.

(** [s ▷ x] is the scope [s] extended with one variable [x].
    You can use index [I0] to refer to [x] and [IS] to refer
    to variables in [s]. *)
Notation "s ▷ x" := (SCons s x) (at level 20, left associativity).

(** [index s] is the type of de Bruijn indices in scope [s].
    You can think of an index as a natural number which
    tells you how many binders to count up (i.e. going towards the root)
    until you find the corresponding variable. *)
Inductive index : scope -> Type :=
| I0 {s x} : index (s ▷ x)
| IS {s x} : index s -> index (s ▷ x).

Derive Signature NoConfusion NoConfusionHom for index.

(** Boolean equality test on de Bruijn indices. *)
Equations index_eq {s} : index s -> index s -> bool :=
index_eq I0 I0 := true ;
index_eq (IS i) (IS i') := index_eq i i' ;
index_eq _ _ := false.

Lemma index_eq_spec {s} (i i' : index s) :
  reflect (i = i') (index_eq i i').
Proof.
funelim (index_eq i i').
- constructor. reflexivity.
- constructor. intros H ; depelim H.
- constructor. intros H ; depelim H.
- destruct H ; constructor.
  + f_equal. assumption.
  + intros H ; depelim H. auto.
Qed.

(***********************************************************************)
(** * Terms. *)
(***********************************************************************)

(** We represente evars using a unique identifier (a natural number). *)
Definition evar_id := nat.

(** Well-scoped terms, using de Bruijn indices. *)
Inductive term : scope -> Type :=
(** [TType] is the type of types (i.e. [Type] in Rocq).
    For the moment we don't support universes or other sorts such as [Prop]. *)
| TType {s} : term s
(** [TVar i] is a local variable, encoded using a de Bruijn indcex [i]. *)
| TVar {s} (i : index s) : term s
(** [TLam x ty body] represents the lambda abstraction [fun x : ty => body]. *)
| TLam {s} (x : tag) (ty : term s) (body : term (s ▷ x)) : term s
(** [TProd x a b] represents the dependent product [forall x : a, b].
    If [b] does not depend on [x] the product is non-dependent: [a -> b]. *)
| TProd {s} (x : tag) (a : term s) (b : term (s ▷ x)) : term s
(** [TApp f args] represents the application of function [f] to the
    list of arguments [args]. Functions are expected to maintain the invariant
    that [args] is non-empty and that [f] is not itself of the form [TApp _ _]. *)
| TApp {s} (f : term s) (args : list (term s)) : term s
(** [TEvar e] represents an existential variable (evar) used for unification.
    Information pertaining to evars is stored in the evar-map. *)
| TEvar {s} (e : evar_id) : term s.

Derive Signature NoConfusion NoConfusionHom for term.

(** Size of a term. *)
Equations term_size {s} : term s -> nat :=
term_size TType := 0 ;
term_size (TVar _) := 0 ;
term_size (TLam x ty body) := term_size ty + term_size body + 1 ;
term_size (TProd x a b) := term_size a + term_size b + 1 ;
term_size (TApp f args) := term_size f + sum (List.map term_size args) + 1 ;
term_size (TEvar _) := 0.

(***********************************************************************)
(** * Renamings. *)
(***********************************************************************)

(** [ren s s'] is the type of renamings from scope [s] to scope [s'].
    We wrap the underlying function [index s -> index s'] in a trivial
    inductive so that we can extract renamings to a more efficient
    representation (indeed closures are not very efficient). *)
Variant ren (s s' : scope) :=
| Ren (r : index s -> index s').

Arguments Ren {s s'}.

(** Apple a renaming to an index. *)
Definition rapply {s s'} (r : ren s s') (i : index s) : index s' :=
  let 'Ren f := r in f i.

(** [rid] is the identity renaming. *)
Definition rid {s} : ren s s :=
  Ren (fun i => i).

(** [rshift] is a renaming which increments every index. *)
Definition rshift {s x} : ren s (s ▷ x) :=
  Ren (fun i => IS i).

(** [rcomp r1 r2] is the composition of [r1] followed by [r2]. *)
Definition rcomp {s1 s2 s3} (r1 : ren s1 s2) (r2 : ren s2 s3) : ren s1 s3 :=
  Ren (fun i => rapply r2 (rapply r1 i)).

Equations rcons_aux {s s' x} (i : index s') (r : ren s s') : index (s ▷ x) -> index s' :=
rcons_aux i r I0 := i ;
rcons_aux i r (IS j) := rapply r j.

(** [rcons i r] is the renaming which maps [0] to [i] and [j+1] to [r i]. *)
Definition rcons {s s' x} (i : index s') (r : ren s s') : ren (s ▷ x) s' :=
  Ren (rcons_aux i r).

(** [rup r] lifts [r] through a binder. *)
Definition rup {s s' x} (r : ren s s') : ren (s ▷ x) (s' ▷ x) :=
  rcons I0 (rcomp r rshift).

(* This is kind of funny: computationally it's the identity,
   but not in the types. *)
Definition replace_tag {s x} (y : tag) : ren (s ▷ x) (s ▷ y).
  destruct x ; destruct y ; exact rid.
Defined.

(** Apply a renaming to a term. *)
Equations rename {s s'} : ren s s' -> term s -> term s' :=
rename r TType := TType ;
rename r (TVar i) := TVar (rapply r i) ;
rename r (TLam x ty body) := TLam x (rename r ty) (rename (rup r) body) ;
rename r (TProd x a b) := TProd x (rename r a) (rename (rup r) b) ;
rename r (TApp f args) := TApp (rename r f) (List.map (rename r) args) ;
rename r (TEvar e) := TEvar e.

(***********************************************************************)
(** * Thinnings. *)
(***********************************************************************)

(** A thinning is an order-preserving renaming. *)
(* TODO: should we use a more efficient representation for identity thinnings? *)
Inductive thinning : scope -> scope -> Type :=
| ThinNil : thinning ∅ ∅
| ThinSkip {s s' x} : thinning s s' -> thinning s (s' ▷ x)
| ThinKeep {s s' x} : thinning s s' -> thinning (s ▷ x) (s' ▷ x).

Derive Signature NoConfusion for thinning.

(** [tid] is the identity thinning. *)
Equations tid {s} : thinning s s :=
@tid ∅ := ThinNil ;
@tid (s ▷ α) := ThinKeep tid.

(** [tcomp δ1 δ2] is the composition of [δ1] followed by [δ2]. *)
Equations tcomp {s s' s''} (δ1 : thinning s s') (δ2 : thinning s' s'') : thinning s s'' :=
tcomp ThinNil δ2 := δ2 ;
tcomp δ1 (ThinSkip δ2) := ThinSkip (tcomp δ1 δ2) ;
tcomp (ThinKeep δ1) (ThinKeep δ2) := ThinKeep (tcomp δ1 δ2) ;
tcomp (ThinSkip δ1) (ThinKeep δ2) := ThinSkip (tcomp δ1 δ2).

(** Lift a thinning through a binder. *)
Definition tup {s s' α} (δ : thinning s s') : thinning (s ▷ α) (s' ▷ α) :=
  ThinKeep δ.

(** Apply a thinning to an index. *)
Equations tapply {s s'} : thinning s s' -> index s -> index s' :=
tapply (ThinSkip δ) i := IS (tapply δ i) ;
tapply (ThinKeep δ) I0 := I0 ;
tapply (ThinKeep δ) (IS i) := IS (tapply δ i).

(** Apply a thinning to a term. *)
Definition thin {s s'} (δ : thinning s s') (t : term s) : term s' :=
  rename (Ren $ tapply δ) t.

Section ThinInv.
  #[local] Notation "f <$> x" := (option_map f x)
    (at level 62, right associativity).

  #[local] Notation "f <*> x" := (option_apply f x)
    (at level 60, right associativity).

  (** [tapply_inv δ i] is the partial inverse of [tapply]: it finds an
      index [i'] if it exists such that [tapply δ i' = i]. *)
  Equations tapply_inv {s s'} : thinning s s' -> index s' -> option (index s) :=
  tapply_inv (ThinSkip δ) I0 := None ;
  tapply_inv (ThinSkip δ) (IS i) := tapply_inv δ i ;
  tapply_inv (ThinKeep δ) I0 := Some I0 ;
  tapply_inv (ThinKeep δ) (IS i) := IS <$> tapply_inv δ i.

  (** [thin_inv δ t'] is the partial inverse of [thin]: if computes a term [t]
      such that [thin δ t = t']. Returns [None] if [t'] uses variables which are
      not in the domain of the thinning [δ]. *)
  Equations thin_inv {s s'} : thinning s s' -> term s' -> option (term s) :=
  thin_inv δ TType := Some TType ;
  thin_inv δ (TVar i) := TVar <$> tapply_inv δ i ;
  thin_inv δ (TLam x ty body) := (TLam x <$> thin_inv δ ty) <*> thin_inv (tup δ) body ;
  thin_inv δ (TProd x a b) := (TProd x <$> thin_inv δ a) <*> thin_inv (tup δ) b ;
  thin_inv δ (TApp f args) := (TApp <$> thin_inv δ f) <*> option_sequence (List.map (thin_inv δ) args) ;
  thin_inv δ (TEvar e) := Some (TEvar e).

End ThinInv.

(***********************************************************************)
(** * Substitutions. *)
(***********************************************************************)

(** [subst s s'] is the type of substitutions from scope [s] to scope [s'].
    We wrap the underlying function [index s -> terl s'] in a trivial
    inductive so that we can extract renamings to a more efficient
    representation (indeed closures are not very efficient). *)
Variant subst (s s' : scope) :=
| Subst (σ : index s -> term s').

Arguments Subst {s s'}.

(** Apply a substitution to an index. *)
Definition sapply {s s'} (σ : subst s s') (i : index s) : term s' :=
  let 'Subst f := σ in f i.

(** [sid] is the identity substitution. *)
Definition sid {s} : subst s s :=
  Subst (fun i => TVar i).

(** [sshift] is the substitution which increments every index. *)
Definition sshift {s α} : subst s (s ▷ α) :=
  Subst (fun i => TVar (IS i)).

(** [srcomp σ r] is the composition of substitution [σ] followed by renaming [r]. *)
Definition srcomp {s1 s2 s3} (σ1 : subst s1 s2) (r2 : ren s2 s3) : subst s1 s3 :=
  Subst (fun i => rename r2 (sapply σ1 i)).

(** [rscomp r σ] is the composition of renaming [r] followed by substitution [σ]. *)
Definition rscomp {s1 s2 s3} (r1 : ren s1 s2) (σ2 : subst s2 s3) : subst s1 s3 :=
  Subst (fun i => sapply σ2 (rapply r1 i)).

Equations scons_aux {s s' x} : term s' -> subst s s' -> index (s ▷ x) -> term s' :=
scons_aux t σ I0 := t ;
scons_aux t σ (IS i) := sapply σ i.

Definition scons {s s' x} (t : term s') (σ : subst s s') : subst (s ▷ x) s' :=
  Subst (scons_aux t σ).

(** [sup σ] lifts [σ] through a binder. *)
Definition sup {s s' x} (σ : subst s s') : subst (s ▷ x) (s' ▷ x) :=
  scons (TVar I0) (srcomp σ rshift).

(** Apply a substitution to a term. *)
Equations substitute {s s'} : subst s s' -> term s -> term s' :=
substitute σ TType := TType ;
substitute σ (TVar i) := sapply σ i ;
substitute σ (TLam x ty body) := TLam x (substitute σ ty) (substitute (sup σ) body) ;
substitute σ (TProd x a b) := TProd x (substitute σ a) (substitute (sup σ) b) ;
substitute σ (TApp f args) := TApp (substitute σ f) (List.map (substitute σ) args) ;
substitute σ (TEvar e) := TEvar e.

(** [scomp σ1 σ2] is the composition of [σ1] followed by [σ2]. *)
Definition scomp {s1 s2 s3} (σ1 : subst s1 s2) (σ2 : subst s2 s3) : subst s1 s3 :=
  Subst (fun i => substitute σ2 (sapply σ1 i)).

(** [t[x := u]] substitutes variable [x] with [u] in [t].
    It assumes the scope of [t] is of the form [_ ▷ x]. *)
Notation "t [ x := u ]" := (substitute (@scons _ _ x u sid) t) (at level 10, only parsing).

(***********************************************************************)
(** * Smart constructors. *)
(***********************************************************************)

(** [ScopeMem x s] states that variable [x] occurs in scope [s]. *)
Class ScopeMem (x : tag) (s : scope) := {
  (** [idx_of x] computes the de Bruijn index associated to variable [x]
      in the current scope. *)
  idx_of : index s
}.
Arguments idx_of x {s} {_}.

#[export] Instance scope_mem_zero x s : ScopeMem x (s ▷ x) := {
  idx_of := I0
}.

#[export] Instance scope_mem_succ x y s : ScopeMem x s -> ScopeMem x (s ▷ y) := {
  idx_of := IS (idx_of x)
}.

(** [ScopeIncl s s'] states that scope [s] is included in scope [s'],
    i.e. that there exists a renaming from [s] to [s']. *)
Class ScopeIncl (s s' : scope) := {
  (** [wk_idx i] weakens index [i] to the current scope. *)
  wk_idx : ren s s'
}.

#[export] Instance scope_incl_refl s : ScopeIncl s s := {
  wk_idx := rid
}.

#[export] Program Instance scope_incl_empty s : ScopeIncl ∅ s := {
  wk_idx := _
}.
Next Obligation. constructor. intros i. depelim i. Defined.

#[export] Instance scope_incl_extend_r x s s' :
  ScopeIncl s s' -> ScopeIncl s (s' ▷ x) := {
  wk_idx := rcomp wk_idx rshift
}.

#[export] Instance scope_incl_extend x s s' :
  ScopeIncl s s' -> ScopeIncl (s ▷ x) (s' ▷ x) := {
  wk_idx := rup wk_idx
}.

(** [wk t] weakens term [t] to the current scope. *)
Definition wk {s s'} `{ScopeIncl s s'} (t : term s) : term s' :=
  rename wk_idx t.
