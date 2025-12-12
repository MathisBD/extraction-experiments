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

(***********************************************************************)
(** * Lifting a property on a spine of arguments. *)
(***********************************************************************)

Section All_spine.
  Context (P : forall s, evar_map -> context ∅ s -> term s -> term s -> Prop).

  (** [All_spine] lifts a typing relation [P] to a spine of arguments. If [P] is [typing],
      then [All_spine Σ Γ f_ty args T] means that appling a function of type [f_ty]
      to the list of arguments [args] yields a term of type [T]. *)
  Inductive All_spine {s} (Σ : evar_map) (Γ : context ∅ s) : term s -> list (term s) -> term s -> Prop :=
  | All_spine_nil f_ty f_ty' :
      Σ ⊢ f_ty ≡ f_ty' ->
      All_spine Σ Γ f_ty [] f_ty'

  | All_spine_cons f_ty x a b arg args T :
      P s Σ Γ (TProd x a b) TType ->
      Σ ⊢ f_ty ≡ TProd x a b ->
      P s Σ Γ arg a ->
      All_spine Σ Γ (b[x := arg]) args T ->
      All_spine Σ Γ f_ty (arg :: args) T.
End All_spine.

Derive Signature for All_spine.

Lemma All_spine_consequence (P Q : forall s, evar_map -> context ∅ s -> term s -> term s -> Prop) :
  (forall s Σ Γ t T, P s Σ Γ t T -> Q s Σ Γ t T) ->
  forall s Σ Γ f_ty args (T : term s),
    All_spine P Σ Γ f_ty args T ->
    All_spine Q Σ Γ f_ty args T.
Proof.
intros Himpl s Σ Γ f_ty args T H. induction H ; econstructor ; eauto.
Qed.

Lemma All_spine_conv_type P {s} Σ Γ f_ty args (T T' : term s) :
  All_spine P Σ Γ f_ty args T ->
  Σ ⊢ T ≡ T' ->
  All_spine P Σ Γ f_ty args T'.
Proof.
intros H. induction H.
- intros H1. constructor. now rewrite <-H1.
- intros H3. econstructor ; eauto.
Qed.

Lemma All_spine_conv_func_type P {s} Σ Γ f_ty f_ty' args (T : term s) :
  All_spine P Σ Γ f_ty args T ->
  Σ ⊢ f_ty ≡ f_ty' ->
  All_spine P Σ Γ f_ty' args T.
Proof.
intros H. induction H.
- intros H1. constructor. now rewrite <-H1.
- intros H3. econstructor ; eauto. now rewrite <-H3.
Qed.

#[export] Instance All_spine_proper_conv_type P s Σ Γ :
  Proper (conv Σ ==> eq ==> conv Σ ==> iff) (@All_spine s P Σ Γ).
Proof.
intros f_ty f_ty' Hfty args args' <- T T' HT. split ; intros H.
- revert HT. apply All_spine_conv_type.
  revert Hfty. now apply All_spine_conv_func_type.
- symmetry in HT, Hfty. revert HT. apply All_spine_conv_type.
  revert Hfty. now apply All_spine_conv_func_type.
Qed.

(***********************************************************************)
(** * Typing relation. *)
(***********************************************************************)

Reserved Notation "Σ ;; Γ ⊢ t : T"
  (at level 50, no associativity, Γ at next level, t at next level, T at next level).

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
    (*args <> [] ->*)
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
    (*is_TApp f = false ->*)
    (*args <> [] ->*)
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
- apply Happ with f_ty ; auto. clear f H. revert f_ty args T H0.
  fix IHspine 4. intros f_ty args T H0. destruct H0.
  + constructor. assumption.
  + econstructor ; [| eassumption | |].
    * split ; [assumption |]. now apply IH.
    * split ; [assumption |]. apply IH. assumption.
    * apply IHspine ; auto.
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
  exists f_ty,
    Σ ;; Γ ⊢ f : f_ty /\
    All_spine (@typing) Σ Γ f_ty args T.
Proof.
intros H. induction H ; intros f' args' Ht ; depelim Ht.
- exists f_ty. split ; auto. revert H0.
  apply All_spine_consequence. clear. firstorder.
- destruct (IHtyping1 f' args' eq_refl) as (f_ty' & Hf & H3).
  exists f_ty'. split ; auto. clear IHtyping1 IHtyping2 H H1 Hf.
  depind H3 ; econstructor ; eauto. now rewrite H.
Qed.

Lemma typing_app_inv {s} Σ Γ f args (T : term s) :
  Σ ;; Γ ⊢ TApp f args : T ->
  exists f_ty,
    Σ ;; Γ ⊢ f : f_ty /\
    All_spine (@typing) Σ Γ f_ty args T.
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
    * rewrite H0. now simpl_subst.
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
(** * Properties of typing. *)
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

Lemma typing_evar_type Σ entry :
  typing_evar_entry Σ entry ->
  Σ ;; CNil ⊢ entry.(evar_type) : TType.
Proof. intros H. destruct H ; cbn ; assumption. Qed.

(** Beta reduction preserves typing. *)
Lemma typing_beta {s} Σ Γ x ty body arg args (T : term s) :
  Σ ;; Γ ⊢ TApp (TLam x ty body) (arg :: args) : T ->
  Σ ;; Γ ⊢ TApp (body[x := arg]) args : T.
Proof.
intros H. apply typing_app_inv in H. destruct H as (f_ty & H1 & H2).
apply typing_lam_inv in H1. destruct H1 as (body_ty & H1 & Hty & Hbody).
depelim H2. assert (x0 = x) as ->. { destruct x0 ; destruct x ; reflexivity. }
rewrite H1 in H0. clear f_ty H1. apply conv_prod_inv in H0. destruct H0 as (H4 & H5).
eapply typing_app with (body_ty[x := arg]).
- eapply typing_substitute ; eauto. apply typing_scons ; simpl_subst.
  + apply typing_conv_type with a ; auto. now symmetry.
  + apply typing_sid.
- rewrite H5. assumption.
Qed.

Lemma typing_evar_expand_helper {s} Σ Γ ev (T : term s) :
  typing_evar_map Σ ->
  Σ ;; Γ ⊢ TEvar ev : T ->
  Σ ;; Γ ⊢ T : TType.
Proof.
intros HΣ H. depind H.
- change TType with (@wk ∅ s _ TType). unfold wk. eapply typing_rename.
  + apply typing_evar_type. apply (HΣ ev entry H).
  + intros i. depelim i.
- assumption.
Qed.

(** Evar expansion preserves typing. *)
Lemma typing_evar_expand {s} Σ Γ ev ty def (T : term s) :
  typing_evar_map Σ ->
  Σ ;; Γ ⊢ TEvar ev : T ->
  Σ ev = Some (mk_evar_entry ty (Some def)) ->
  Σ ;; Γ ⊢ wk def : T.
Proof.
intros H1 H2 H3. pose proof (HT := typing_evar_expand_helper _ _ _ _ H1 H2).
specialize (H1 _ _ H3). depelim H1.
apply typing_evar_inv in H2. destruct H2 as (entry & H4 & H5).
rewrite H4 in H3. depelim H3. cbn in H5. apply typing_conv_type with (wk ty).
- unfold wk. eapply typing_rename ; eauto. intros i. depelim i.
- now symmetry.
- assumption.
Qed.

(** Reducing a term doesn't change its type. *)
Lemma typing_red1 {s} Σ Γ (t u T : term s) :
  typing_evar_map Σ ->
  typing_context Σ Γ ->
  Σ ;; Γ ⊢ t : T ->
  Σ ⊢ t ~>₁ u ->
  Σ ;; Γ ⊢ u : T.
Proof.
intros HΣ HΓ Ht Hred. depind Hred.
- eapply typing_beta ; eauto.
- eapply typing_evar_expand ; eauto.
- (*apply typing_lam_inv in Ht. destruct Ht as (body_ty & H1 & Hty & Hbody).
  apply IHHred in Hty ; auto. rewrite Hred in H1.
  apply typing_conv_type with (TProd x ty' body_ty).
  + apply typing_lam.
    * assumption.
    *

  apply typing_lam. apply IHHred.*)


apply HΣ in H. depelim H.  depelim Ht. apply typing_evar_entry.

Admitted.

(** In a typing derivation, the type is itself well-typed. *)
Lemma typing_type_ok {s} Σ Γ (t T : term s) :
  typing_evar_map Σ ->
  typing_context Σ Γ ->
  Σ ;; Γ ⊢ t : T ->
  Σ ;; Γ ⊢ T : TType.
Proof.
intros Hevm Hctx Ht. induction Ht.
- constructor.
- rewrite <-H. now apply typing_lookup_context.
- constructor ; auto. apply IHHt2 ; auto. constructor ; auto.
- constructor.
- clear f H Ht. depind H0 ; [auto |]. apply IHAll_spine. intros _ _.
  destruct H as [H _].
  assert (Σ ;; Γ ⊢ a : TType) by admit.
  assert (Σ ;; CCons Γ x a ⊢ b : TType) by admit.
  change TType with (TType [x := arg]). eapply typing_substitute.
  + eassumption.
  + apply typing_scons.
    * simpl_subst. apply H1.
    * apply typing_sid.
- unfold wk. change (@TType s) with (@rename ∅ s wk_idx TType).
  eapply typing_rename.
  + apply typing_evar_type. now apply (Hevm ev).
  + intros i. depelim i.
- assumption.
Admitted.


(** Changing a term to a convertible one doesn't change its type. *)
Lemma typing_conv {s} Σ Γ (t u T : term s) :
  Σ ;; Γ ⊢ t : T ->
  Σ ⊢ t ≡ u ->
  Σ ;; Γ ⊢ u : T.
Proof. Admitted.

#[export] Instance typing_conv_Proper {s} Σ Γ :
  Proper (conv Σ ==> eq ==> iff) (@typing s Σ Γ).
Proof.
intros t t' Ht T T' ->. split ; intros H ; eapply typing_conv ; eauto. now symmetry.
Qed.
