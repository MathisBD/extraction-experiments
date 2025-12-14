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
(** * Lifting a property on a spine of arguments. *)
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

Reserved Notation "Σ ;; Γ ⊢ t : T"
  (at level 50, no associativity, Γ at next level, t at next level, T at next level).

Unset Elimination Schemes.

(** [Σ ;; Γ ⊢ t : T] means that [t] has type [T] under context [Γ] in evar-map [Σ]. *)
Inductive typing {s} (Σ : evar_map) (Γ : context ∅ s) : term s -> term s -> Prop :=

| typing_type :
    Σ ;; Γ ⊢ TType : TType

| typing_var i ty :
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
(** * Typing renamings and substitutions. *)
(***********************************************************************)

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
(** * Typing local contexts. *)
(***********************************************************************)

(** [typing_context Σ Γ] means that the types in context [Γ] are well-typed. *)
Inductive typing_context (Σ : evar_map) : forall {s}, context ∅ s -> Prop :=
| typing_context_nil : typing_context Σ CNil
| typing_context_cons {s} Γ x (ty : term s) :
    typing_context Σ Γ ->
    Σ ;; Γ ⊢ ty : TType ->
    typing_context Σ (CCons Γ x ty).

Derive Signature for typing_context.

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
    All_spine Σ (fun t T => Σ ;; Γ ⊢ t : T /\ P s Σ Γ t T) f_ty args T ->
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
- apply Happ with f_ty ; auto. clear f H. revert f_ty args T H0.
  fix IHspine 4. intros f_ty args T H0. destruct H0.
  + constructor.
  + econstructor ; eauto.
- apply Hevar ; auto.
- eapply Hconv_type ; eauto.
Qed.

(***********************************************************************)
(** * Inverting typing derivations. *)
(***********************************************************************)

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
- now rewrite H.
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
  + clear IHHt Ht. depind H ; cbn ; [constructor ; now rewrite H |].
    apply All_spine_cons with (x := x) (a := rename ρ a) (b := rename (rup x ρ) b).
    * simpl_subst in H. now apply H.
    * rewrite H0. simpl_subst. reflexivity.
    * now apply H1.
    * simpl_subst. simpl_subst in IHAll_spine. apply IHAll_spine ; auto.
- now apply typing_evar.
- apply typing_conv_type with (A := rename ρ A) ; auto. now rewrite H.
Qed.

(***********************************************************************)
(** * Compatibility of typing with substitution. *)
(***********************************************************************)

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
  clear f Ht IHHt. depind H ; [constructor ; now rewrite H |]. cbn.
  apply All_spine_cons with (x := x) (a := substitute σ a) (b := substitute (sup x σ) b).
  + simpl_subst in H. now apply H.
  + rewrite H0. simpl_subst. reflexivity.
  + now apply H1.
  + simpl_subst. simpl_subst in IHAll_spine. now apply IHAll_spine.
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
    eapply typing_rename ; eauto. apply typing_rshift.
  + change TType with (rename (@rshift s x) TType).
    eapply typing_rename ; eauto. apply typing_rshift.
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
  typing_context Σ Γ ->
  Σ ;; Γ ⊢ t : T ->
  Σ ;; Γ ⊢ T : TType.
Proof.
intros HΣ HΓ H. induction H.
- constructor.
- rewrite <-H. now apply typing_lookup_context.
- constructor ; auto. apply IHtyping2 ; auto. now constructor.
- constructor.
- specialize (IHtyping HΣ HΓ).
  assert (H1 : All_spine Σ (fun t T => Σ ;; Γ ⊢ t : T /\ Σ ;; Γ ⊢ T : TType) f_ty args T).
  { revert H0. apply All_spine_consequence. firstorder. }
  clear H H0. induction H1.
  + assumption.
  + apply IHAll_spine. destruct H as (H & _). apply typing_prod_inv in H.
    destruct H as (_ & Ha & Hb). change TType with (TType[x := arg]).
    eapply typing_substitute ; eauto. apply typing_scons ; [|apply typing_sid].
    simpl_subst. apply H1.
- change TType with (@wk ∅ s _ TType). unfold wk. eapply typing_rename.
  + apply typing_evar_type. now apply (HΣ ev).
  + intros i. depelim i.
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
    apply conv_substitute. rewrite H0, H3 in Hf'. now apply conv_prod_inv in Hf'.
- apply typing_evar_inv in HA'. destruct HA' as (entry' & Hentry & HA').
  rewrite H in Hentry. depelim Hentry. now symmetry.
- rewrite <-H. now apply IHHA1.
Qed.