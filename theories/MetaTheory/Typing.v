From Metaprog Require Import Prelude.
From Metaprog Require Export Data.Context MetaTheory.Conversion.

(** This module defines the typing relation on terms and its basic
    properties, notably:
    - Compatibility with renaming and substitution.
    - Inversion lemmas.
    - The validity lemma: in any typing derivation the type is itself well-typed.
    - Uniqueness of types up to conversion.

    This module also defines a notion of typing for various data-types
    such as contexts, evar-maps, renamings, and substitutions.
*)

(***********************************************************************)
(** * Lifting typing on a context. *)
(***********************************************************************)

Section All_context.
  Context (P : forall s, context ∅ s -> term s -> term s -> Prop).

  (** [All_context] lifts a typing relation [P] to a context. If [P] is [typing],
      then [All_context P Γ] means that the context [Γ] only contains well-typed terms. *)
  Inductive All_context : forall {s}, context ∅ s -> Prop :=
  | All_context_nil : All_context CNil

  | All_context_cons {s} (Γ : context ∅ s) x ty :
      All_context Γ ->
      P s Γ ty TType ->
      All_context (CCons Γ x ty).
End All_context.

Derive Signature for All_context.

Lemma All_context_consequence (P Q : forall s, context ∅ s -> term s -> term s -> Prop) :
  (forall s Γ t T, P s Γ t T -> Q s Γ t T) ->
  forall s (Γ : context ∅ s), All_context P Γ -> All_context Q Γ.
Proof.
intros Himpl s Γ H. induction H ; econstructor ; eauto.
Qed.

(***********************************************************************)
(** * Lifting typing on a spine of arguments. *)
(***********************************************************************)

Section All_spine.
  Context {s : scope} (Σ : evar_map).
  Context (P : term s -> term s -> Prop).

  (** [All_spine] lifts a typing relation [P] to a spine of arguments. If [P] is [typing],
      then [All_spine Σ P f_ty args T] means that appling a function of type [f_ty]
      to the list of arguments [args] yields a term of type [T]. *)
  Inductive All_spine : term s -> list (term s) -> term s -> Prop :=
  | All_spine_nil f_ty : All_spine f_ty [] f_ty

  | All_spine_cons f_ty x a b arg args T :
      P (TProd x a b) TType ->
      Σ ⊢ f_ty ≡ TProd x a b ->
      P arg a ->
      All_spine (b[x := arg]) args T ->
      All_spine f_ty (arg :: args) T.
End All_spine.

Derive Signature for All_spine.

Lemma All_spine_consequence {s} Σ (P Q : term s -> term s -> Prop) :
  (forall t T, P t T -> Q t T) ->
  forall f_ty args (T : term s),
    All_spine Σ P f_ty args T ->
    All_spine Σ Q f_ty args T.
Proof.
intros Himpl f_ty args T H. induction H ; econstructor ; eauto.
Qed.

(*Lemma All_spine_conv_type {s} Σ P f_ty args (T T' : term s) :
  All_spine Σ P f_ty args T ->
  Σ ⊢ T ≡ T' ->
  P T' TType ->
  All_spine Σ P f_ty args T'.
Proof.
intros H. induction H.
- intros H1 H2. constructor ; [now rewrite <-H1 | assumption].
- intros H3 H4. econstructor ; eauto.
Qed.

Lemma All_spine_conv_func_type {s} Σ P f_ty f_ty' args (T : term s) :
  All_spine Σ P f_ty args T ->
  Σ ⊢ f_ty ≡ f_ty' ->
  All_spine Σ P f_ty' args T.
Proof.
intros H. induction H.
- intros H1. constructor ; [now rewrite <-H1 | assumption].
- intros H3. econstructor ; eauto. now rewrite <-H3.
Qed.

#[export] Instance All_spine_proper_conv_func_type s Σ P :
  Proper (conv Σ ==> eq ==> eq ==> iff) (@All_spine s Σ P).
Proof.
intros f_ty f_ty' Hfty args args' <- T T' <-. split ; intros H.
- revert Hfty. now apply All_spine_conv_func_type.
- symmetry in Hfty. revert Hfty. now apply All_spine_conv_func_type.
Qed.*)

(***********************************************************************)
(** * Typing relation. *)
(***********************************************************************)

Unset Elimination Schemes.

Reserved Notation "Σ ;; Γ ⊢ t : T"
  (at level 50, no associativity, Γ at next level, t at next level, T at next level).

(** [Σ ;; Γ ⊢ t : T] means that [t] has type [T] under context [Γ] in evar-map [Σ]. *)
Inductive typing (Σ : evar_map) {s} (Γ : context ∅ s) : term s -> term s -> Prop :=

| typing_type :
    All_context (@typing Σ) Γ ->
    Σ ;; Γ ⊢ TType : TType

| typing_var i ty :
    All_context (@typing Σ) Γ ->
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
    All_spine Σ (typing Σ Γ) f_ty args T ->
    Σ ;; Γ ⊢ TApp f args : T

| typing_evar ev entry :
    All_context (@typing Σ) Γ ->
    Σ ev = Some entry ->
    Σ ;; Γ ⊢ TEvar ev : wk entry.(evar_type)

| typing_conv_type t A B :
    Σ ;; Γ ⊢ t : A ->
    Σ ⊢ A ≡ B ->
    Σ ;; Γ ⊢ B : TType ->
    Σ ;; Γ ⊢ t : B

where "Σ ;; Γ ⊢ t : T" := (typing Σ Γ t T).

Set Elimination Schemes.

Derive Signature for typing.

(***********************************************************************)
(** * Typing local contexts. *)
(***********************************************************************)

(** [typing_context Σ Γ] means that the types in context [Γ] are well-typed. *)
Definition typing_context (Σ : evar_map) {s} (Γ : context ∅ s) :=
  All_context (@typing Σ) Γ.

(***********************************************************************)
(** * Typing renamings and substitutions. *)
(***********************************************************************)

(** [Σ ;; Γ ⊢ᵣ ρ : Δ] means that the renaming [ρ] maps well-typed terms
    in context [Γ] to well-typed terms in context [Δ]. *)
Definition typing_ren {s s'} (Σ : evar_map) (Γ : context ∅ s) (ρ : ren s s') (Δ : context ∅ s') :=
  typing_context Σ Γ /\
  typing_context Σ Δ /\
  forall i, rename ρ (lookup_context i Γ) = lookup_context (rapply ρ i) Δ.

Notation "Σ ;; Γ ⊢ᵣ ρ : Δ" := (typing_ren Σ Γ ρ Δ)
  (at level 50, Γ at next level, ρ at next level, Δ at next level).

(** [Σ ;; Γ ⊢ₛ σ : Δ] means that the substitution [σ] maps well-typed
    terms in context [Γ] to well-typed terms in context [Δ]. *)
Definition typing_subst {s s'} Σ (Γ : context ∅ s) (σ : subst s s') (Δ : context ∅ s') :=
  typing_context Σ Γ /\
  typing_context Σ Δ /\
  forall i, Σ ;; Δ ⊢ sapply σ i : substitute σ (lookup_context i Γ).

Notation "Σ ;; Γ ⊢ₛ σ : Δ" := (typing_subst Σ Γ σ Δ)
  (at level 50, Γ at next level, σ at next level, Δ at next level).

(***********************************************************************)
(** * Typing evar-maps. *)
(***********************************************************************)

(** [typing_evar_entry Σ e] asserts that the evar-entry [e] is well-typed
    in evar-map [Σ]. *)
Inductive typing_evar_entry (Σ : evar_map) : evar_entry -> Prop :=

(** An undefined evar entry is well-typed if the type if well-typed. *)
| typing_evar_undefined ty :
    Σ ;; CNil ⊢ ty : TType ->
    typing_evar_entry Σ (mk_evar_entry ty None)

(** A defined evar entry is well-typed if the type is well-typed
    and the definition has the correct type. *)
| typing_evar_defined ty def :
    Σ ;; CNil ⊢ ty : TType ->
    Σ ;; CNil ⊢ def : ty ->
    typing_evar_entry Σ (mk_evar_entry ty (Some def)).

Derive Signature for typing_evar_entry.

(** [typing_evar_map Σ] means that the evar-map [Σ] is well-typed.
    We do _not_ check that the evar-map is acyclic:
    this would likely be very annoying to do. *)
Definition typing_evar_map (Σ : evar_map) :=
  forall ev entry, Σ ev = Some entry -> typing_evar_entry Σ entry.

(***********************************************************************)
(** * Induction principle for [typing]. *)
(***********************************************************************)

(** Induction principle for [typing]. *)
Lemma typing_ind
  (P : evar_map -> forall s, context ∅ s -> term s -> term s -> Prop)
  (Htype : forall s Σ Γ,
    All_context (fun s' Γ' t T => Σ ;; Γ' ⊢ t : T /\ P Σ s' Γ' t T) Γ ->
    P Σ s Γ TType TType)
  (Hvar : forall s Σ Γ i ty,
    All_context (fun s' Γ' t T => Σ ;; Γ' ⊢ t : T /\ P Σ s' Γ' t T) Γ ->
    lookup_context i Γ = ty ->
    P Σ s Γ (TVar i) ty)
  (Hlam : forall s Σ Γ x ty body body_ty,
    Σ ;; Γ ⊢ ty : TType -> P Σ s Γ ty TType ->
    Σ ;; CCons Γ x ty ⊢ body : body_ty -> P Σ (s ▷ x) (CCons Γ x ty) body body_ty ->
    P Σ s Γ (TLam x ty body) (TProd x ty body_ty))
  (Hprod : forall s Σ Γ x a b,
    Σ ;; Γ ⊢ a : TType -> P Σ s Γ a TType ->
    Σ ;; CCons Γ x a ⊢ b : TType -> P Σ (s ▷ x) (CCons Γ x a) b TType ->
    P Σ s Γ (TProd x a b) TType)
  (Happ : forall s Σ Γ f f_ty args T,
    Σ ;; Γ ⊢ f : f_ty -> P Σ s Γ f f_ty ->
    All_spine Σ (fun t T => Σ ;; Γ ⊢ t : T /\ P Σ s Γ t T) f_ty args T ->
    P Σ s Γ (TApp f args) T)
  (Hevar : forall s Σ Γ ev entry,
    All_context (fun s' Γ' t T => Σ ;; Γ' ⊢ t : T /\ P Σ s' Γ' t T) Γ ->
    Σ ev = Some entry ->
    P Σ s Γ (TEvar ev) (wk entry.(evar_type)))
  (Hconv_type : forall s Σ Γ t A B,
    Σ ;; Γ ⊢ t : A -> P Σ s Γ t A ->
    Σ ⊢ A ≡ B ->
    Σ ;; Γ ⊢ B : TType -> P Σ s Γ B TType ->
    P Σ s Γ t B) :
  forall Σ s Γ t T, Σ ;; Γ ⊢ t : T -> P Σ s Γ t T.
Proof.
fix IH 6. intros Σ s Γ t T H. depelim H.
- apply Htype. revert s Γ H. fix IHctx 3. intros s Γ H. destruct H ; constructor.
  + apply IHctx. assumption.
  + split ; auto.
- apply Hvar ; auto. subst. clear i. revert s Γ H. fix IHctx 3. intros s Γ H. destruct H ; constructor.
  + apply IHctx. assumption.
  + split ; auto.
- apply Hlam ; auto.
- apply Hprod ; auto.
- apply Happ with f_ty ; auto. clear f H. revert f_ty args T H0.
  fix IHspine 4. intros f_ty args T H0. destruct H0.
  + constructor.
  + econstructor ; eauto.
- apply Hevar ; auto. revert s Γ H. fix IHctx 3. intros s Γ H. destruct H ; constructor.
  + apply IHctx. assumption.
  + split ; auto.
- eapply Hconv_type ; eauto.
Qed.

(***********************************************************************)
(** * Inverting typing derivations. *)
(***********************************************************************)

Lemma typing_context_validity {s} Σ Γ (t T : term s) :
  Σ ;; Γ ⊢ t : T ->
  typing_context Σ Γ.
Proof.
intros H. induction H ; auto.
all: revert H ; now apply All_context_consequence.
Qed.

(** Inverting typing derivations is not completely trivial:
    indeed typing looks syntax directed at first glance, but in fact
    it is _not_ because of the rule [typing_conv_type]. *)

Lemma typing_type_inv {s} Σ Γ T :
  Σ ;; Γ ⊢ TType : T ->
  Σ ⊢ T ≡ @TType s.
Proof.
intros H. depind H.
- reflexivity.
- now rewrite <-H0.
Qed.

Lemma typing_var_inv {s} Σ Γ (i : index s) T :
  Σ ;; Γ ⊢ TVar i : T ->
  Σ ⊢ T ≡ lookup_context i Γ.
Proof.
intros H. depind H.
- now subst.
- now rewrite <-H0.
Qed.

Lemma typing_lam_inv_aux {s x} Σ Γ (t : term s) T :
  Σ ;; Γ ⊢ t : T ->
  forall ty body, t = TLam x ty body ->
  exists body_ty,
    Σ ⊢ T ≡ TProd x ty body_ty /\
    Σ ;; Γ ⊢ ty : TType /\
    Σ ;; CCons Γ x ty ⊢ body : body_ty.
Proof.
intros H. induction H ; intros ty' body' Ht ; depelim Ht.
- exists body_ty. now split3.
- destruct (IHtyping1 ty' body' eq_refl) as (body_ty' & HA & Hty & Hbody).
  exists body_ty'. split3 ; auto. now rewrite <-H0.
Qed.

Lemma typing_lam_inv {s x} Σ Γ (ty : term s) body T :
  Σ ;; Γ ⊢ TLam x ty body : T ->
  exists body_ty,
    Σ ⊢ T ≡ TProd x ty body_ty /\
    Σ ;; Γ ⊢ ty : TType /\
    Σ ;; CCons Γ x ty ⊢ body : body_ty.
Proof. intros H. eapply typing_lam_inv_aux ; eauto. Qed.

Lemma typing_prod_inv_aux {s x} Σ Γ (t : term s) T :
  Σ ;; Γ ⊢ t : T ->
  forall a b, t = TProd x a b ->
    Σ ⊢ T ≡ TType /\
    Σ ;; Γ ⊢ a : TType /\
    Σ ;; CCons Γ x a ⊢ b : TType.
Proof.
intros H. induction H ; intros a' b' Ht ; depelim Ht.
- now split3.
- destruct (IHtyping1 a' b' eq_refl) as (HA & Ha & Hb).
  split3 ; auto. now rewrite <-H0.
Qed.

Lemma typing_prod_inv {s x} Σ Γ (a : term s) b T :
  Σ ;; Γ ⊢ TProd x a b : T ->
  Σ ⊢ T ≡ TType /\ Σ ;; Γ ⊢ a : TType /\ Σ ;; CCons Γ x a ⊢ b : TType.
Proof. intros H. eapply typing_prod_inv_aux ; eauto. Qed.

Lemma typing_app_inv_aux {s} Σ Γ t (T : term s) :
  Σ ;; Γ ⊢ t : T ->
  forall f args, t = TApp f args ->
  exists f_ty T',
    Σ ;; Γ ⊢ f : f_ty /\
    All_spine Σ (typing Σ Γ) f_ty args T' /\
    Σ ⊢ T' ≡ T.
Proof.
intros H. induction H ; intros f' args' Ht ; depelim Ht.
- assert (H1 : All_spine Σ (typing Σ Γ) f_ty args T).
  { revert H0. apply All_spine_consequence. firstorder. }
  clear IHtyping H0. exists f_ty, T. now split3.
- destruct (IHtyping1 f' args' eq_refl) as (f_ty' & T' & Hf & H3).
  exists f_ty', T'. split3 ; auto.
  + apply H3.
  + rewrite <-H0. apply H3.
Qed.

Lemma typing_app_inv {s} Σ Γ f args (T : term s) :
  Σ ;; Γ ⊢ TApp f args : T ->
  exists f_ty T',
    Σ ;; Γ ⊢ f : f_ty /\
    All_spine Σ (typing Σ Γ) f_ty args T' /\
    Σ ⊢ T' ≡ T.
Proof. intros H. eapply typing_app_inv_aux ; eauto. Qed.

Lemma typing_evar_inv {s} Σ Γ ev (T : term s) :
  Σ ;; Γ ⊢ TEvar ev : T ->
  exists entry,
    Σ ev = Some entry /\
    Σ ⊢ T ≡ wk entry.(evar_type).
Proof.
intros H. depind H.
- exists entry. now split.
- destruct IHtyping1 as (entry & H2 & H3). exists entry.
  split ; auto. now rewrite <-H0.
Qed.

(***********************************************************************)
(** * Compatibility of typing with renaming. *)
(***********************************************************************)

Lemma typing_rid {s} Σ (Γ : context ∅ s) :
  typing_context Σ Γ ->
  Σ ;; Γ ⊢ᵣ rid : Γ.
Proof. intros H. split3 ; auto. intros i. simpl_subst. reflexivity. Qed.

Lemma typing_rshift {s x} Σ (Γ : context ∅ s) ty :
  typing_context Σ (CCons Γ x ty) ->
  typing_ren Σ Γ rshift (CCons Γ x ty).
Proof.
intros H. split3 ; auto. now depelim H.
Qed.

Lemma typing_rcons {s s' x} Σ (Γ : context ∅ s) (Δ : context ∅ s') i ρ ty :
  Σ ;; Γ ⊢ ty : TType ->
  rename ρ ty = lookup_context i Δ ->
  Σ ;; Γ ⊢ᵣ ρ : Δ ->
  Σ ;; CCons Γ x ty ⊢ᵣ rcons x i ρ : Δ.
Proof.
intros H1 H2 H3. split3.
- constructor.
  + apply H3.
  + apply H1.
- apply H3.
- intros j. depelim j ; simpl_subst ; simp lookup_context ; simpl_subst.
  + assumption.
  + apply H3.
Qed.

Lemma typing_rcomp {s s' s''} Σ Γ Δ E (ρ1 : ren s s') (ρ2 : ren s' s'') :
  Σ ;; Γ ⊢ᵣ ρ1 : Δ ->
  Σ ;; Δ ⊢ᵣ ρ2 : E ->
  Σ ;; Γ ⊢ᵣ rcomp ρ1 ρ2 : E.
Proof.
intros H1 H2. split3.
- apply H1.
- apply H2.
- intros i. simpl_subst. rewrite <-rename_rename.
  destruct H1 as (_ & _ & H1). rewrite H1.
  destruct H2 as (_ & _ & H2). rewrite H2.
  reflexivity.
Qed.

Lemma typing_rup {s s' x} Σ Γ Δ (ρ : ren s s') ty :
  Σ ;; Γ ⊢ ty : TType ->
  Σ ;; Δ ⊢ rename ρ ty : TType ->
  Σ ;; Γ ⊢ᵣ ρ : Δ ->
  Σ ;; CCons Γ x ty ⊢ᵣ rup x ρ : CCons Δ x (rename ρ ty).
Proof.
intros H1 H2 H3. unfold rup. apply typing_rcons.
- assumption.
- simp lookup_context. now simpl_subst.
- eapply typing_rcomp ; eauto. apply typing_rshift. constructor.
  + apply H3.
  + apply H2.
Qed.

(** Compatibility of typing with renaming. *)
Lemma typing_rename {s s'} Σ Γ Δ (ρ : ren s s') t T :
  Σ ;; Γ ⊢ t : T ->
  Σ ;; Γ ⊢ᵣ ρ : Δ ->
  Σ ;; Δ ⊢ rename ρ t : rename ρ T.
Proof.
intros Ht Hρ. induction Ht in s', ρ, Δ, Hρ |- * ; simpl_subst.
- apply typing_type. apply Hρ.
- subst. destruct Hρ as (Hρ1 & Hρ2 & Hρ3). rewrite Hρ3. constructor ; auto.
- apply typing_lam ; auto using typing_rup.
- apply typing_prod ; auto using typing_rup.
- eapply typing_app.
  + now apply IHHt.
  + clear IHHt Ht. depind H ; cbn ; [constructor ; now rewrite H |].
    apply All_spine_cons with (x := x) (a := rename ρ a) (b := rename (rup x ρ) b).
    * simpl_subst in H. now apply H.
    * rewrite H0. simpl_subst. reflexivity.
    * now apply H1.
    * simpl_subst. simpl_subst in IHAll_spine. apply IHAll_spine ; auto.
- apply typing_evar ; auto. apply Hρ.
- apply typing_conv_type with (A := rename ρ A) ; auto. now rewrite H.
Qed.

(***********************************************************************)
(** * Compatibility of typing with substitution. *)
(***********************************************************************)

Lemma typing_sid {s} Σ (Γ : context ∅ s) :
  typing_context Σ Γ ->
  Σ ;; Γ ⊢ₛ sid : Γ.
Proof. intros H. split3 ; auto. intros i. simpl_subst. now constructor. Qed.

Lemma typing_sshift {s x} Σ (Γ : context ∅ s) ty :
  typing_context Σ (CCons Γ x ty) ->
  Σ ;; Γ ⊢ₛ sshift : CCons Γ x ty.
Proof.
intros H. split3 ; auto.
- now depelim H.
- simpl_subst. constructor ; auto.
Qed.

Lemma typing_scons {s s' x} Σ (Γ : context ∅ s) (Δ : context ∅ s') t σ ty :
  Σ ;; Γ ⊢ ty : TType ->
  Σ ;; Δ ⊢ t : substitute σ ty ->
  Σ ;; Γ ⊢ₛ σ : Δ ->
  Σ ;; CCons Γ x ty ⊢ₛ scons x t σ : Δ.
Proof.
intros H1 H2 H3. split3.
- constructor ; auto. apply H3.
- apply H3.
- intros i. depelim i ; simpl_subst ; simp lookup_context.
  + simpl_subst. assumption.
  + simpl_subst. destruct H3 as (HΔ & HΓ & H3). apply H3.
Qed.

Lemma typing_srcomp {s s' s''} Σ Γ Δ E (σ : subst s s') (ρ : ren s' s'') :
  Σ ;; Γ ⊢ₛ σ : Δ ->
  Σ ;; Δ ⊢ᵣ ρ : E ->
  Σ ;; Γ ⊢ₛ srcomp σ ρ : E.
Proof.
intros H1 H2. split3.
- apply H1.
- apply H2.
- intros i. simpl_subst. rewrite <-rename_substitute.
  eapply typing_rename ; [|eassumption]. apply H1.
Qed.

Lemma typing_sup {s s' x} Σ Γ Δ (σ : subst s s') ty :
  Σ ;; Γ ⊢ ty : TType ->
  Σ ;; Δ ⊢ substitute σ ty : TType ->
  Σ ;; Γ ⊢ₛ σ : Δ ->
  Σ ;; CCons Γ x ty ⊢ₛ sup x σ : CCons Δ x (substitute σ ty).
Proof.
intros H1 H2 H3. unfold sup. apply typing_scons.
- apply H1.
- constructor.
  + constructor ; auto. apply H3.
  + simp lookup_context. simpl_subst. reflexivity.
- eapply typing_srcomp ; eauto. apply typing_rshift. constructor ; auto. apply H3.
Qed.

Lemma typing_substitute {s s'} Σ Γ Δ (σ : subst s s') t T :
  Σ ;; Γ ⊢ t : T ->
  Σ ;; Γ ⊢ₛ σ : Δ ->
  Σ ;; Δ ⊢ substitute σ t : substitute σ T.
Proof.
intros Ht Hσ. induction Ht in s', σ, Δ, Hσ |- * ; simpl_subst.
- constructor. apply Hσ.
- subst. apply Hσ.
- apply typing_lam ; auto using typing_sup.
- apply typing_prod ; auto using typing_sup.
- apply typing_app with (f_ty := substitute σ f_ty) ; auto.
  clear f Ht IHHt. depind H ; [constructor ; now rewrite H |]. cbn.
  apply All_spine_cons with (x := x) (a := substitute σ a) (b := substitute (sup x σ) b).
  + simpl_subst in H. now apply H.
  + rewrite H0. simpl_subst. reflexivity.
  + now apply H1.
  + simpl_subst. simpl_subst in IHAll_spine. now apply IHAll_spine.
- econstructor ; eauto. apply Hσ.
- eapply typing_conv_type ; eauto. now rewrite H.
Qed.

Lemma typing_rscomp {s s' s''} Σ Γ Δ E (ρ : ren s s') (σ : subst s' s'') :
  Σ ;; Γ ⊢ᵣ ρ : Δ ->
  Σ ;; Δ ⊢ₛ σ : E ->
  Σ ;; Γ ⊢ₛ rscomp ρ σ : E.
Proof.
intros H1 H2. split3.
- apply H1.
- apply H2.
- intros i. rewrite <-substitute_rename.
  assert (sapply (rscomp ρ σ) i = substitute σ (TVar (rapply ρ i))) as -> by now simpl_subst.
  eapply typing_substitute ; eauto. destruct H1 as (_ & _ & H1). rewrite H1.
  constructor ; auto. apply H2.
Qed.

Lemma typing_scomp {s s' s''} Σ Γ Δ E (σ1 : subst s s') (σ2 : subst s' s'') :
  Σ ;; Γ ⊢ₛ σ1 : Δ ->
  Σ ;; Δ ⊢ₛ σ2 : E ->
  Σ ;; Γ ⊢ₛ scomp σ1 σ2 : E.
Proof.
intros H1 H2. split3.
- apply H1.
- apply H2.
- intros i. simpl_subst. rewrite <-substitute_substitute.
  eapply typing_substitute ; eauto. apply H1.
Qed.

(***********************************************************************)
(** * Properties of context typing. *)
(***********************************************************************)

Lemma typing_lookup_context {s} Σ (Γ : context ∅ s) i :
  typing_context Σ Γ ->
  Σ ;; Γ ⊢ lookup_context i Γ : TType.
Proof.
intros H. induction H.
- depelim i.
- depelim i ; simp lookup_context ; simpl_subst.
  + change TType with (rename (@rshift s x) TType).
    eapply typing_rename ; eauto. apply typing_rshift. constructor ; auto.
  + change TType with (rename (@rshift s x) TType).
    eapply typing_rename ; eauto. apply typing_rshift. constructor ; auto.
Qed.

(***********************************************************************)
(** * Properties of evar-map typing. *)
(***********************************************************************)

Lemma typing_evar_type Σ entry :
  typing_evar_entry Σ entry ->
  Σ ;; CNil ⊢ entry.(evar_type) : TType.
Proof. intros H. destruct H ; cbn ; assumption. Qed.

(***********************************************************************)
(** * Validity lemma. *)
(***********************************************************************)

(** The validity lemma for typing states that in any typing derivation,
    the type is well-typed. *)
Lemma typing_validity {s} Σ Γ (t T : term s) :
  typing_evar_map Σ ->
  Σ ;; Γ ⊢ t : T ->
  Σ ;; Γ ⊢ T : TType.
Proof.
intros HΣ H. induction H.
- constructor. revert H. apply All_context_consequence. firstorder.
- subst. apply typing_lookup_context. revert H.
  apply All_context_consequence. firstorder.
- constructor ; auto.
- constructor. eapply typing_context_validity ; eauto.
- specialize (IHtyping HΣ).
  assert (H1 : All_spine Σ (fun t T => Σ ;; Γ ⊢ t : T /\ Σ ;; Γ ⊢ T : TType) f_ty args T).
  { revert H0. apply All_spine_consequence. firstorder. }
  clear H H0. induction H1.
  + assumption.
  + apply IHAll_spine. destruct H as (H & _). apply typing_prod_inv in H.
    destruct H as (_ & Ha & Hb). change TType with (TType[x := arg]).
    eapply typing_substitute ; eauto. apply typing_scons.
    * assumption.
    * simpl_subst. apply H1.
    * apply typing_sid. eapply typing_context_validity ; eauto.
- simpl_subst. change TType with (@rename ∅ s wk_idx TType). eapply typing_rename.
  + apply typing_evar_type. now apply (HΣ ev).
  + split3.
    * constructor.
    * revert H. apply All_context_consequence. firstorder.
    * intros i. depelim i.
- assumption.
Qed.

(*(** This is a more powerful version of rule [typing_conv_type']: it does not
    require proving that the new type [B] is well-typed. *)
Lemma typing_conv_type' {s} Σ Γ (t A B : term s) :
  Σ ;; Γ ⊢ t : A ->
  Σ ⊢ A ≡ B ->
  Σ ;; Γ ⊢ t : B.
Proof.
intros Ht Hconv. eapply typing_conv_type.
- eassumption.
- assumption.
- eapply
*)
(* Actually this needs compatibility of typing with conversion... *)

(***********************************************************************)
(** * Uniqueness of types. *)
(***********************************************************************)

(** Types are unique (up to convertibility). This lemma will no longer be true
    once we add subtyping (with universes). *)
Lemma typing_unique_type {s} Σ Γ (t A A' : term s) :
  Σ ;; Γ ⊢ t : A ->
  Σ ;; Γ ⊢ t : A' ->
  Σ ⊢ A ≡ A'.
Proof.
intros HA. revert A'. induction HA ; intros A' HA'.
- apply typing_type_inv in HA'. now symmetry.
- subst. apply typing_var_inv in HA'. now symmetry.
- apply typing_lam_inv in HA'. destruct HA' as (body_ty' & HA' & Hty & Hbody).
  rewrite HA'. f_equiv. apply IHHA2. assumption.
- apply typing_prod_inv in HA'. now symmetry.
- apply typing_app_inv in HA'. destruct HA' as (f_ty' & T' & Hf' & Hspine & H1).
  apply IHHA in Hf'. rewrite <-H1.
  assert (H2 : All_spine Σ (typing Σ Γ) f_ty args T).
  { revert H. apply All_spine_consequence. firstorder. }
  clear A' H1 IHHA H HA. induction args in f_ty, f_ty', Hf', Hspine, H2 |- *.
  + depelim Hspine ; depelim H2. assumption.
  + depelim Hspine ; depelim H2. eapply IHargs ; [| eassumption.. ].
    assert (x0 = x) as ->. { destruct x0 ; destruct x ; reflexivity. }
    f_equiv. rewrite H0, H3 in Hf'. now apply conv_prod_inv in Hf'.
- apply typing_evar_inv in HA'. destruct HA' as (entry' & Hentry & HA').
  rewrite H0 in Hentry. depelim Hentry. now symmetry.
- rewrite <-H. now apply IHHA1.
Qed.