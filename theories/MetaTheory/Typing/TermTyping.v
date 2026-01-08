From Metaprog Require Import Prelude.
From Metaprog Require Export Data.Context MetaTheory.Conversion.ContextConversion.

(** This module defines the typing relations on terms and contexts
    and their basic properties, notably inversion lemmas.
*)

(***********************************************************************)
(** * Lifting a typing-like relation on a context. *)
(***********************************************************************)

Section All_context.
  Context (P : forall s, context ∅ s -> term s -> term s -> Prop).

  (** [All_context P Γ] lifts the relation [P] over the context [Γ]. *)
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

Lemma All_context_and {P Q : forall s, context ∅ s -> term s -> term s -> Prop} {s} {Γ : context ∅ s} :
  All_context (fun s Γ t T => P s Γ t T /\ Q s Γ t T) Γ ->
  (All_context P Γ /\ All_context Q Γ).
Proof.
induction Γ.
- constructor ; constructor.
- intros H. depelim H. apply IHΓ in H. split ; now constructor.
Qed.

(***********************************************************************)
(** * Lifting a typing-like relation on a spine of arguments. *)
(***********************************************************************)

Section All_spine.
  Context (Σ : evar_map) {s : scope}.
  Context (P : term s -> term s -> Prop).

  (** [All_spine Σ P] lifts the relation [P] to a spine of arguments.
      If [P] is [typing Σ Γ], then [All_spine Σ P f_ty args T] means
      that appling a function of type [f_ty] to the list of arguments
      [args] yields a term of type [T]. *)
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

Lemma All_spine_consequence {Σ s} {P Q : term s -> term s -> Prop} :
  (forall t T, P t T -> Q t T) ->
  forall f_ty args (T : term s),
    All_spine Σ P f_ty args T ->
    All_spine Σ Q f_ty args T.
Proof.
intros Himpl f_ty args T H. induction H ; econstructor ; eauto.
Qed.

(** In [All_spine Σ P f_ty args T] we can change the function type [f_ty]
    to a convertible one, as long as we are willing to accept that the return
    type [T] also changes to a convertible one. *)
Lemma All_spine_conv_func_type {Σ s} P f_ty f_ty' args (T : term s) :
  All_spine Σ P f_ty args T ->
  Σ ⊢ f_ty ≡ f_ty' ->
  exists T',
    All_spine Σ P f_ty' args T' /\
    Σ ⊢ T ≡ T'.
Proof.
intros Hspine Hconv. induction Hspine in f_ty', Hconv |- *.
- exists f_ty'. split ; [constructor | assumption].
- specialize (IHHspine (b[x := arg])). forward IHHspine by reflexivity.
  destruct IHHspine as (T' & Hspine' & HconvT).
  exists T'. split ; auto. econstructor ; eauto. now rewrite <-Hconv.
Qed.

Lemma All_spine_app {Σ s} P (A B C : term s) args args' :
  All_spine Σ P A args B ->
  All_spine Σ P B args' C ->
  All_spine Σ P A (args ++ args') C.
Proof.
intros H H'. depind H ; cbn.
- assumption.
- econstructor ; eauto.
Qed.

Lemma All_spine_extend_evm {Σ1 Σ2 s P} {T T' : term s} {args} :
  Σ1 ⊑ Σ2 ->
  All_spine Σ1 P T args T' ->
  All_spine Σ2 P T args T'.
Proof.
intros HΣ H. depind H ; econstructor ; eauto.
now apply (conv_extend_evm HΣ).
Qed.

(***********************************************************************)
(** * Typing relation on terms. *)
(***********************************************************************)

Reserved Notation "Σ ;; Γ ⊢ t : T"
  (at level 50, no associativity, Γ, t, T at next level).

Reserved Notation "'ctyping' Σ Γ"
  (at level 9, no associativity, Σ, Γ at next level).

Reserved Notation "'spine_typing' Σ Γ f_ty args T"
  (at level 9, Σ, Γ, f_ty, args, T at next level).

Unset Elimination Schemes.

(** [Σ ;; Γ ⊢ t : T] means that [t] has type [T] under context [Γ] in evar-map [Σ].

    [ctyping Σ Γ] means that context [Γ] only contains well-typed types.
    [ctyping] is a notation on top of [All_context].

    [spine_typing Σ Γ f_ty args T] means that applying a function of type [f_ty]
    to arguments [args] results in a term of type [T].
    [spine_typing] is a notation on top of [All_spine].
*)
Inductive typing (Σ : evar_map) {s} (Γ : context ∅ s) : term s -> term s -> Prop :=

| typing_type :
    ctyping Σ Γ ->
    Σ ;; Γ ⊢ TType : TType

| typing_var i ty :
    ctyping Σ Γ ->
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
    spine_typing Σ Γ f_ty args T ->
    Σ ;; Γ ⊢ TApp f args : T

| typing_evar ev entry ty :
    ctyping Σ Γ ->
    Σ ev = Some entry ->
    wk entry.(evar_type) = ty ->
    Σ ;; Γ ⊢ TEvar ev : ty

| typing_conv_type t A B :
    Σ ;; Γ ⊢ t : A ->
    Σ ⊢ A ≡ B ->
    Σ ;; Γ ⊢ B : TType ->
    Σ ;; Γ ⊢ t : B

where "Σ ;; Γ ⊢ t : T" := (typing Σ Γ t T)
   and "'ctyping' Σ Γ" := (All_context (@typing Σ) Γ)
   and "'spine_typing' Σ Γ f_ty args T" := (All_spine Σ (typing Σ Γ) f_ty args T).

Set Elimination Schemes.

Derive Signature for typing.

(***********************************************************************)
(** * Induction principle for [typing]. *)
(***********************************************************************)

(** Induction principle for [typing]. *)
Lemma typing_ind (Σ : evar_map)
  (P : forall s, context ∅ s -> term s -> term s -> Prop)
  (Htype : forall s Γ,
    All_context (fun s' Γ' t T => Σ ;; Γ' ⊢ t : T /\ P s' Γ' t T) Γ ->
    P s Γ TType TType)
  (Hvar : forall s Γ i ty,
    All_context (fun s' Γ' t T => Σ ;; Γ' ⊢ t : T /\ P s' Γ' t T) Γ ->
    lookup_context i Γ = ty ->
    P s Γ (TVar i) ty)
  (Hlam : forall s Γ x ty body body_ty,
    Σ ;; Γ ⊢ ty : TType -> P s Γ ty TType ->
    Σ ;; CCons Γ x ty ⊢ body : body_ty -> P (s ▷ x) (CCons Γ x ty) body body_ty ->
    P s Γ (TLam x ty body) (TProd x ty body_ty))
  (Hprod : forall s Γ x a b,
    Σ ;; Γ ⊢ a : TType -> P s Γ a TType ->
    Σ ;; CCons Γ x a ⊢ b : TType -> P (s ▷ x) (CCons Γ x a) b TType ->
    P s Γ (TProd x a b) TType)
  (Happ : forall s Γ f f_ty args T,
    Σ ;; Γ ⊢ f : f_ty -> P s Γ f f_ty ->
    All_spine Σ (fun t T => Σ ;; Γ ⊢ t : T /\ P s Γ t T) f_ty args T ->
    P s Γ (TApp f args) T)
  (Hevar : forall s Γ ev entry,
    All_context (fun s' Γ' t T => Σ ;; Γ' ⊢ t : T /\ P s' Γ' t T) Γ ->
    Σ ev = Some entry ->
    P s Γ (TEvar ev) (wk entry.(evar_type)))
  (Hconv_type : forall s Γ t A B,
    Σ ;; Γ ⊢ t : A -> P s Γ t A ->
    Σ ⊢ A ≡ B ->
    Σ ;; Γ ⊢ B : TType -> P s Γ B TType ->
    P s Γ t B) :
  forall s Γ t T, Σ ;; Γ ⊢ t : T -> P s Γ t T.
Proof.
fix IH 5. intros s Γ t T H. depelim H.
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
- subst. apply Hevar ; auto. revert s Γ H. fix IHctx 3. intros s Γ H. destruct H ; constructor.
  + apply IHctx. assumption.
  + split ; auto.
- eapply Hconv_type ; eauto.
Qed.

(***********************************************************************)
(** * Basic properties of [typing]. *)
(***********************************************************************)

(** In any typing derivation [Σ ;; Γ ⊢ t : T] the context [Γ] is well-typed. *)
Lemma typing_context_validity {s} Σ Γ (t T : term s) :
  Σ ;; Γ ⊢ t : T ->
  ctyping Σ Γ.
Proof.
intros H. induction H ; auto.
all: revert H ; now apply All_context_consequence.
Qed.

Lemma typing_extend_evm {Σ1 Σ2 s Γ} :
  Σ1 ⊑ Σ2 ->
  subrelation (@typing Σ1 s Γ) (@typing Σ2 s Γ).
Proof.
intros HΣ t T H. induction H.
- constructor. revert H. apply All_context_consequence. firstorder.
- constructor ; auto. revert H. apply All_context_consequence. firstorder.
- now constructor.
- now constructor.
- apply typing_app with f_ty ; auto. apply (All_spine_extend_evm HΣ).
  revert H0. apply All_spine_consequence. firstorder.
- pose proof (Hev := evm_incl_prop _ _ HΣ ev). rewrite H0 in Hev. depelim Hev.
  + cbn. eapply typing_evar ; eauto.
    revert H. apply All_context_consequence. firstorder.
  + cbn. eapply typing_evar ; eauto.
    revert H. apply All_context_consequence. firstorder.
- apply typing_conv_type with A ; auto. now apply (conv_extend_evm HΣ).
Qed.

Lemma ctyping_extend_evm {Σ1 Σ2 s} {Γ : context ∅ s} :
  Σ1 ⊑ Σ2 ->
  ctyping Σ1 Γ ->
  ctyping Σ2 Γ.
Proof.
intros HΣ H. depind H ; constructor ; auto. now apply (typing_extend_evm HΣ).
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
(** * Well-typed judgement. *)
(***********************************************************************)

(** [well_typed Σ Γ t] means that term [t] is well-typed for some
    (unknown) type. *)
Definition well_typed (Σ : evar_map) {s} (Γ : context ∅ s) (t : term s) : Prop :=
  exists T, Σ ;; Γ ⊢ t : T.

Lemma well_typed_extend_evm {Σ1 Σ2 s} {Γ : context ∅ s} {t} :
  Σ1 ⊑ Σ2 ->
  well_typed Σ1 Γ t ->
  well_typed Σ2 Γ t.
Proof.
intros HΣ (T & Ht). exists T. now apply (typing_extend_evm HΣ).
Qed.

(***********************************************************************)
(** * Inversion lemmas for [well_typed]. *)
(***********************************************************************)

(** The following lemmas are not always the most precise:
    they lose the relationships between the types of a term
    and of its subterm.
    Consider reasoning directly on [typing] if needed.
*)

Lemma well_typed_lam {s x} Σ (Γ : context ∅ s) ty body :
  well_typed Σ Γ (TLam x ty body) ->
  well_typed Σ Γ ty /\ well_typed Σ (CCons Γ x ty) body.
Proof.
intros (T & H). apply typing_lam_inv in H. firstorder.
Qed.

Lemma well_typed_prod {s x} Σ (Γ : context ∅ s) a b :
  well_typed Σ Γ (TProd x a b) ->
  well_typed Σ Γ a /\ well_typed Σ (CCons Γ x a) b.
Proof.
intros (T & H). apply typing_prod_inv in H. firstorder.
Qed.

Lemma well_typed_app Σ {s} (Γ : context ∅ s) f args :
  well_typed Σ Γ (TApp f args) ->
  well_typed Σ Γ f /\ Forall (well_typed Σ Γ) args.
Proof.
intros (T & H). apply typing_app_inv in H. destruct H as (f_ty & T' & Hf & Hspine & _).
split ; [firstorder |]. clear f Hf. depind Hspine ; constructor ; firstorder.
Qed.