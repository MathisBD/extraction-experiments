From Metaprog Require Import Prelude.
From Metaprog Require Import Data.Context MetaTheory.Conversion.

(** This module defines the typing relation on terms. *)

(***********************************************************************)
(** * Basic definitions. *)
(***********************************************************************)

(*Definition is_TApp {s} (t : term s) : bool :=
  match t with
  | TApp _ _ => true
  | _ => false
  end.

Lemma is_TApp_rename {s s'} (ρ : ren s s') t :
  is_TApp (rename ρ t) = is_TApp t.
Proof.
induction t using term_ind' in s', ρ |- * ; simpl_subst ; cbn ; auto.
Qed.*)

(** [All_context P Γ] means that [P Γ' ty] holds on every type [Γ' ⊢ ty]
    in the context [Γ]. *)
Inductive All_context {s} (P : forall s', context s s' -> term s' -> Prop) :
  forall {s'}, context s s' -> Prop :=
| All_context_nil : All_context P CNil
| All_context_cons {s'} Γ x (ty : term s') :
    All_context P Γ -> P s' Γ ty -> All_context P (CCons Γ x ty).

Section All_spine.
  Context (P : forall s, evar_map -> context ∅ s -> term s -> term s -> Prop).

  (** [All_spine] lifts a typing relation [P] to a spine of arguments. If [P] is [typing],
      then [All_spine Σ Γ f_ty args T] means that appling a function of type [f_ty]
      to the list of arguments [args] yields a term of type [T]. *)
  Inductive All_spine {s} (Σ : evar_map) (Γ : context ∅ s) : term s -> list (term s) -> term s -> Prop :=
  | All_spine_nil f_ty :
      All_spine Σ Γ f_ty [] f_ty

  | All_spine_cons f_ty x a b arg args T :
      P s Σ Γ (TProd x a b) TType ->
      Σ ⊢ f_ty ≡ TProd x a b ->
      All_spine Σ Γ (b[x := arg]) args T ->
      All_spine Σ Γ f_ty (arg :: args) T.
End All_spine.

(***********************************************************************)
(** * Typing relation. *)
(***********************************************************************)

Reserved Notation "Σ ;; Γ ⊢ t : T"
  (at level 50, no associativity, Γ at next level, t at next level, T at next level).

Reserved Notation "'typing_context' Σ Γ"
  (at level 9, no associativity, Σ at next level, Γ at next level).

Unset Elimination Schemes.

(** [Σ ;; Γ ⊢ t : T] means that [t] has type [T] under context [Γ] in evar-map [Σ]. *)
Inductive typing {s} (Σ : evar_map) (Γ : context ∅ s) : term s -> term s -> Prop :=

| typing_type :
    (*typing_context Σ Γ ->*)
    Σ ;; Γ ⊢ TType : TType

| typing_var i ty :
    (*typing_context Σ Γ ->*)
    lookup_context i Γ = ty ->
    Σ ;; Γ ⊢ TVar i : ty

| typing_lam x ty body body_ty :
    Σ ;; Γ ⊢ ty : TType ->
    Σ ;; CCons Γ x ty ⊢ body : body_ty ->
    Σ ;; Γ ⊢ TLam x ty body : TProd x ty body_ty

| typing_prod x a b :
    Σ ;; Γ ⊢ a : TType ->
    Σ ;; CCons Γ x a ⊢ b : TType ->
    Σ ;; Γ ⊢ TProd x a b : TType

| typing_app f f_ty args T :
    Σ ;; Γ ⊢ f : f_ty ->
    (*is_TApp f = false ->*)
    args <> [] ->
    All_spine (@typing) Σ Γ f_ty args T ->
    Σ ;; Γ ⊢ TApp f args : T

| typing_evar ev entry :
    (*typing_context Σ Γ ->*)
    Σ ev = Some entry ->
    Σ ;; Γ ⊢ TEvar ev : wk entry.(evar_type)

| typing_conv_type t A B :
    Σ ;; Γ ⊢ t : A ->
    Σ ⊢ A ≡ B ->
    Σ ;; Γ ⊢ B : TType ->
    Σ ;; Γ ⊢ t : B

where "Σ ;; Γ ⊢ t : T" := (typing Σ Γ t T)
  (*and "'typing_context' Σ Γ" := (All_context (fun _ Γ' t => Σ ;; Γ' ⊢ t : TType) Γ)*).

Set Elimination Schemes.

Derive Signature for typing.

(** [Σ ;; Γ ⊢ᵣ ρ : Δ] means that the renaming [ρ] maps well-typed terms
    in context [Γ] to well-typed terms in context [Δ]. *)
Definition typing_ren {s s'} (Σ : evar_map) (Γ : context ∅ s) (ρ : ren s s') (Δ : context ∅ s') :=
  forall i, rename ρ (lookup_context i Γ) = lookup_context (rapply ρ i) Δ.

Notation "Σ ;; Γ ⊢ᵣ ρ : Δ" := (typing_ren Σ Γ ρ Δ)
  (at level 50, Γ at next level, ρ at next level, Δ at next level).

(** [Σ ;; Γ ⊢ₛ σ : Δ] means that the substitution [σ] maps well-typed
    terms in context [Γ] to well-typed terms in context [Δ]. *)
Definition typing_subst {s s'} Σ (Γ : context ∅ s) (σ : subst s s') (Δ : context ∅ s') :=
  forall i, Σ ;; Δ ⊢ sapply σ i : substitute σ (lookup_context i Γ).

Notation "Σ ;; Γ ⊢ₛ σ : Δ" := (typing_subst Σ Γ σ Δ)
  (at level 50, Γ at next level, σ at next level, Δ at next level).

(***********************************************************************)
(** * Induction principle for [typing]. *)
(***********************************************************************)

(** Induction principle for [typing]. *)
Lemma typing_ind
  (P : forall s, evar_map -> context ∅ s -> term s -> term s -> Prop)
  (Htype : forall s Σ Γ, P s Σ Γ TType TType)
  (Hvar : forall s Σ Γ i ty, lookup_context i Γ = ty -> P s Σ Γ (TVar i) ty)
  (Hlam : forall s Σ Γ x ty body body_ty,
    Σ ;; Γ ⊢ ty : TType -> P s Σ Γ ty TType ->
    Σ ;; CCons Γ x ty ⊢ body : body_ty -> P (s ▷ x) Σ (CCons Γ x ty) body body_ty ->
    P s Σ Γ (TLam x ty body) (TProd x ty body_ty))
  (Hprod : forall s Σ Γ x a b,
    Σ ;; Γ ⊢ a : TType -> P s Σ Γ a TType ->
    Σ ;; CCons Γ x a ⊢ b : TType -> P (s ▷ x) Σ (CCons Γ x a) b TType ->
    P s Σ Γ (TProd x a b) TType)
  (Happ : forall s Σ Γ f f_ty args T,
    Σ ;; Γ ⊢ f : f_ty -> P s Σ Γ f f_ty ->
    (*is_TApp f = false ->*)
    args <> [] ->
    All_spine (fun s Σ Γ t T => Σ ;; Γ ⊢ t : T /\ P s Σ Γ t T) Σ Γ f_ty args T ->
    P s Σ Γ (TApp f args) T)
  (Hevar : forall s Σ Γ ev entry,
    Σ ev = Some entry ->
    P s Σ Γ (TEvar ev) (wk entry.(evar_type)))
  (Hconv_type : forall s Σ Γ t A B,
    Σ ;; Γ ⊢ t : A -> P s Σ Γ t A ->
    Σ ⊢ A ≡ B ->
    Σ ;; Γ ⊢ B : TType -> P s Σ Γ B TType ->
    P s Σ Γ t B) :
  forall s Σ Γ t T, Σ ;; Γ ⊢ t : T -> P s Σ Γ t T.
Proof.
fix IH 6. intros s Σ Γ t T H. depelim H.
- apply Htype.
- now apply Hvar.
- apply Hlam ; auto.
- apply Hprod ; auto.
- apply Happ with f_ty ; auto. clear f H H0. revert f_ty args T H1.
  fix IHspine 4. intros f_ty args T H1. destruct H1.
  + constructor.
  + econstructor ; [|eassumption|].
    * split ; [assumption |]. apply IH. assumption.
    * apply IHspine ; auto.
- apply Hevar ; auto.
- eapply Hconv_type ; eauto.
Qed.

(***********************************************************************)
(** * Compatibility of typing with renaming and substitution. *)
(***********************************************************************)

Lemma typing_rid {s} Σ (Γ : context ∅ s) :
  Σ ;; Γ ⊢ᵣ rid : Γ.
Proof. intros i. simpl_subst. reflexivity. Qed.

Lemma typing_rshift {s x} Σ (Γ : context ∅ s) ty :
  typing_ren Σ Γ rshift (CCons Γ x ty).
Proof.
intros i. simpl_subst. simp lookup_context. simpl_subst. reflexivity.
Qed.

Lemma typing_rcons {s s' x} Σ (Γ : context ∅ s) (Δ : context ∅ s') i ρ ty :
  rename ρ ty = lookup_context i Δ ->
  Σ ;; Γ ⊢ᵣ ρ : Δ ->
  Σ ;; CCons Γ x ty ⊢ᵣ rcons x i ρ : Δ.
Proof.
intros H1 H2 j. depelim j ; simpl_subst ; simp lookup_context ; simpl_subst.
- assumption.
- apply H2.
Qed.

Lemma typing_rcomp {s s' s''} Σ Γ Δ E (ρ1 : ren s s') (ρ2 : ren s' s'') :
  Σ ;; Γ ⊢ᵣ ρ1 : Δ ->
  Σ ;; Δ ⊢ᵣ ρ2 : E ->
  Σ ;; Γ ⊢ᵣ rcomp ρ1 ρ2 : E.
Proof.
intros H1 H2 i. rewrite <-rename_rename. rewrite H1, H2. now simpl_subst.
Qed.

Lemma typing_rup {s s' x} Σ Γ Δ (ρ : ren s s') ty :
  Σ ;; Γ ⊢ᵣ ρ : Δ ->
  Σ ;; CCons Γ x ty ⊢ᵣ rup x ρ : CCons Δ x (rename ρ ty).
Proof.
intros H. unfold rup. apply typing_rcons.
- simp lookup_context. now simpl_subst.
- eapply typing_rcomp ; eauto. apply typing_rshift.
Qed.

(** Compatibility of typing with renamings *)
Lemma typing_rename {s s'} Σ Γ Δ (ρ : ren s s') t T :
  Σ ;; Γ ⊢ t : T ->
  Σ ;; Γ ⊢ᵣ ρ : Δ ->
  Σ ;; Δ ⊢ rename ρ t : rename ρ T.
Proof.
intros Ht Hρ. induction Ht in s', ρ, Δ, Hρ |- * ; simpl_subst.
- apply typing_type.
- rewrite <-H, Hρ. now constructor.
- apply typing_lam ; auto using typing_rup.
- apply typing_prod ; auto using typing_rup.
- eapply typing_app.
  + now apply IHHt.
  + now depelim args.
  + clear H IHHt Ht. depind H0 ; cbn.
    * constructor.
    * destruct H as [H H'].
      apply All_spine_cons with (x := x) (a := rename ρ a) (b := rename (rup x ρ) b).
      --simpl_subst in H'. now apply H'.
      --rewrite H0. now simpl_subst.
      --simpl_subst. simpl_subst in IHAll_spine. now apply IHAll_spine.
- now apply typing_evar.
- apply typing_conv_type with (A := rename ρ A) ; auto. now rewrite H.
Qed.

Lemma typing_sid {s} Σ (Γ : context ∅ s) :
  Σ ;; Γ ⊢ₛ sid : Γ.
Proof. intros i. simpl_subst. constructor. reflexivity. Qed.

Lemma typing_sshift {s x} Σ (Γ : context ∅ s) ty :
  Σ ;; Γ ⊢ₛ sshift : CCons Γ x ty.
Proof.
intros i. simpl_subst. constructor. simp lookup_context.
unfold wk. cbn. simpl_subst. rewrite <-substitute_sren. reflexivity.
Qed.

Lemma typing_scons {s s' x} Σ (Γ : context ∅ s) (Δ : context ∅ s') t σ ty :
  Σ ;; Δ ⊢ t : substitute σ ty ->
  Σ ;; Γ ⊢ₛ σ : Δ ->
  Σ ;; CCons Γ x ty ⊢ₛ scons x t σ : Δ.
Proof.
intros H1 H2 i. depelim i ; simpl_subst ; simp lookup_context.
- unfold wk. cbn. simpl_subst. assumption.
- unfold wk. cbn. simpl_subst. apply H2.
Qed.

Lemma typing_srcomp {s s' s''} Σ Γ Δ E (σ : subst s s') (ρ : ren s' s'') :
  Σ ;; Γ ⊢ₛ σ : Δ ->
  Σ ;; Δ ⊢ᵣ ρ : E ->
  Σ ;; Γ ⊢ₛ srcomp σ ρ : E.
Proof.
intros H1 H2 i. simpl_subst. rewrite <-rename_substitute.
eapply typing_rename ; [|eassumption]. apply H1.
Qed.

Lemma typing_sup {s s' x} Σ Γ Δ (σ : subst s s') ty :
  Σ ;; Γ ⊢ₛ σ : Δ ->
  Σ ;; CCons Γ x ty ⊢ₛ sup x σ : CCons Δ x (substitute σ ty).
Proof.
intros H. unfold sup. apply typing_scons.
- constructor. simp lookup_context. unfold wk. cbn. simpl_subst. reflexivity.
- eapply typing_srcomp ; eauto. apply typing_rshift.
Qed.

Lemma typing_substitute {s s'} Σ Γ Δ (σ : subst s s') t T :
  Σ ;; Γ ⊢ t : T ->
  Σ ;; Γ ⊢ₛ σ : Δ ->
  Σ ;; Δ ⊢ substitute σ t : substitute σ T.
Proof.
intros Ht Hσ. induction Ht in s', σ, Δ, Hσ |- * ; simpl_subst.
- constructor.
- rewrite <-H. apply Hσ.
- apply typing_lam ; auto using typing_sup.
- apply typing_prod ; auto using typing_sup.
- apply typing_app with (f_ty := substitute σ f_ty) ; auto.
  + depelim args ; auto. intros H' ; depelim H'.
  + clear f Ht IHHt H. depind H0 ; [constructor |]. cbn.
    apply All_spine_cons with (x := x) (a := substitute σ a) (b := substitute (sup x σ) b).
    * simpl_subst in H. now apply H.
    * rewrite H0. simpl_subst. reflexivity.
    * simpl_subst. simpl_subst in IHAll_spine. now apply IHAll_spine.
- econstructor ; eauto.
- eapply typing_conv_type ; eauto. now rewrite H.
Qed.

Lemma typing_rscomp {s s' s''} Σ Γ Δ E (ρ : ren s s') (σ : subst s' s'') :
  Σ ;; Γ ⊢ᵣ ρ : Δ ->
  Σ ;; Δ ⊢ₛ σ : E ->
  Σ ;; Γ ⊢ₛ rscomp ρ σ : E.
Proof.
intros H1 H2 i. rewrite <-substitute_rename.
assert (sapply (rscomp ρ σ) i = substitute σ (TVar (rapply ρ i))) as -> by now simpl_subst.
eapply typing_substitute ; eauto. rewrite H1. now constructor.
Qed.

Lemma typing_scomp {s s' s''} Σ Γ Δ E (σ1 : subst s s') (σ2 : subst s' s'') :
  Σ ;; Γ ⊢ₛ σ1 : Δ ->
  Σ ;; Δ ⊢ₛ σ2 : E ->
  Σ ;; Γ ⊢ₛ scomp σ1 σ2 : E.
Proof.
intros H1 H2 i. simpl_subst. rewrite <-substitute_substitute.
eapply typing_substitute ; eauto.
Qed.

(** Next define typing on evar-maps... *)


Lemma typing_type_ok {s} Σ Γ (t T : term s) :
  Σ ;; Γ ⊢ t : T ->
  Σ ;; Γ ⊢ T : TType.
Proof. Admitted.

(** Reducing a term doesn't change its type. *)
Lemma typing_red {s} Σ Γ (t u T : term s) :
  Σ ;; Γ ⊢ t : T ->
  Σ ⊢ t ~> u ->
  Σ ;; Γ ⊢ u : T.
Proof. Admitted.

(** Changing a term to a convertible one doesn't change its type. *)
Lemma typing_conv {s} Σ Γ (t u T : term s) :
  Σ ;; Γ ⊢ t : T ->
  Σ ⊢ t ≡ u ->
  Σ ;; Γ ⊢ u : T.
Proof. Admitted.
