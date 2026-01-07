From Metaprog Require Import Prelude.
From Metaprog.MetaTheory Require Export Reduction.Confluence.

(** This module defines the conversion relation [conv] on terms
    and proves basic lemmas, notably:
    - The Church-Rosser lemma.
    - Congruence lemmas.
    - Inversion lemmas (aka injectivity of constructors). *)

(***********************************************************************)
(** * Conversion relation on terms. *)
(***********************************************************************)

Reserved Notation "Σ ⊢ t ≡{ f } u"
  (at level 50, no associativity, t at next level, u at next level).

(** Conversion relation on terms, defined as the smallest equivalence
    relation containing [red1]. *)
Inductive conv (flags : red_flags) (Σ : evar_map) {s} : term s -> term s -> Prop :=
| conv_of_red1 t1 t2 : Σ ⊢ t1 ~>{flags} t2 -> Σ ⊢ t1 ≡{flags} t2
| conv_refl t : Σ ⊢ t ≡{flags} t
| conv_sym t1 t2 : Σ ⊢ t1 ≡{flags} t2 -> Σ ⊢ t2 ≡{flags} t1
| conv_trans t1 t2 t3 : Σ ⊢ t1 ≡{flags} t2 -> Σ ⊢ t2 ≡{flags} t3 -> Σ ⊢ t1 ≡{flags} t3

where "Σ ⊢ t ≡{ f } u" := (conv f Σ t u).

Derive Signature for conv.

Notation "Σ ⊢ t ≡ u" := (conv red_flags_all Σ t u)
  (at level 50, no associativity, t at next level, u at next level).

(***********************************************************************)
(** * Typeclass instances for setoid rewriting. *)
(***********************************************************************)

#[export] Instance conv_Reflexive flags Σ s : Reflexive (@conv flags Σ s).
Proof. intros t. apply conv_refl. Qed.

#[export] Instance conv_Symmetric flags Σ s : Symmetric (@conv flags Σ s).
Proof. intros t1 t2. apply conv_sym. Qed.

#[export] Instance conv_Transitive flags Σ s : Transitive (@conv flags Σ s).
Proof. intros t. apply conv_trans. Qed.

Lemma conv_of_red flags Σ {s} (t u : term s) :
  Σ ⊢ t ~~>{flags} u -> Σ ⊢ t ≡{flags} u.
Proof.
intros H. induction H.
- reflexivity.
- rewrite IHred. now apply conv_of_red1.
Qed.

#[export] Instance subrelation_red1_conv flags Σ s :
  subrelation (@red1 flags Σ s) (@conv flags Σ s).
Proof. intros t u H. now apply conv_of_red1. Qed.

#[export] Instance subrelation_red1_conv_flip flags Σ s :
  subrelation (Basics.flip (@red1 flags Σ s)) (@conv flags Σ s).
Proof.
intros t u H. unfold Basics.flip in H. symmetry.
now apply conv_of_red1.
Qed.

#[export] Instance subrelation_red_conv flags Σ s :
  subrelation (@red flags Σ s) (@conv flags Σ s).
Proof. intros t u H. now apply conv_of_red. Qed.

#[export] Instance subrelation_red_conv_flip flags Σ s :
  subrelation (Basics.flip (@red flags Σ s)) (@conv flags Σ s).
Proof.
intros t u H. unfold Basics.flip in H. symmetry.
now apply conv_of_red.
Qed.

Lemma conv_extend_flags {flags1 flags2 Σ s} :
  red_flags_incl flags1 flags2 ->
  subrelation (@conv flags1 Σ s) (@conv flags2 Σ s).
Proof.
intros Hf t u H. induction H.
- apply (red1_extend_flags Hf) in H. now constructor.
- reflexivity.
- now symmetry.
- etransitivity ; eauto.
Qed.

(***********************************************************************)
(** * Church-Rosser lemma. *)
(***********************************************************************)

(** The Church-Rosser lemma is a direct consequence of the confluence lemma.
    Using Church-Rosser, one can lift many lemmas from [red] to [conv]. *)
Lemma church_rosser {flags Σ s} (t1 t2 : term s) :
  Σ ⊢ t1 ≡{flags} t2 ->
  exists u, Σ ⊢ t1 ~~>{flags} u /\ Σ ⊢ t2 ~~>{flags} u.
Proof.
intros H. depind H.
- exists t2. split ; [now apply red_of_red1 | reflexivity].
- exists t. now split.
- destruct IHconv as (u & H1 & H2). exists u. now split.
- destruct IHconv1 as (u1 & H1 & H2). destruct IHconv2 as (u2 & H3 & H4).
  destruct (red_confluence t2 u1 u2 H2 H3) as (u & H5 & H6).
  exists u. split ; etransitivity ; eassumption.
Qed.

(***********************************************************************)
(** * Congruence lemmas. *)
(***********************************************************************)

Section CongruenceLemmas.
  Context {flags : red_flags} {Σ : evar_map} {s : scope}.

  Lemma conv_beta x (ty : term s) body arg args :
    flags.(beta) = true ->
    Σ ⊢ TApp (TLam x ty body) (arg :: args) ≡{flags} TApp (body[x := arg]) args.
  Proof. intros H. now rewrite red_beta. Qed.

  #[export] Instance conv_lam_congr x :
    Proper (conv flags Σ ==> conv flags Σ ==> conv flags Σ) (@TLam s x).
  Proof.
  intros ty ty' Hty body body' Hbody. transitivity (TLam x ty' body).
  - clear Hbody. induction Hty.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  - clear Hty. induction Hbody.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  Qed.

  #[export] Instance conv_prod_congr x :
    Proper (conv flags Σ ==> conv flags Σ ==> conv flags Σ) (@TProd s x).
  Proof.
  intros a a' Ha b b' Hb. transitivity (TProd x a' b).
  - clear Hb. induction Ha.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  - clear Ha. induction Hb.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  Qed.

  Lemma conv_app_congr_aux (f : term s) l (args args' : list (term s)) :
    All2 (conv flags Σ) args args' ->
    Σ ⊢ TApp f (l ++ args) ≡{flags} TApp f (l ++ args').
  Proof.
  intros H. revert f l. depind H ; intros f l.
  - reflexivity.
  - transitivity (TApp f (l ++ y :: xs)).
    + clear IHAll2 H0. induction H.
      * apply conv_of_red1, red1_app_r. apply OnOne2_app_r, OnOne2_head. assumption.
      * reflexivity.
      * now symmetry.
      * etransitivity ; eauto.
    + specialize (IHAll2 f (l ++ [y])). rewrite <-!app_assoc in IHAll2.
      cbn in IHAll2. exact IHAll2.
  Qed.

  #[export] Instance conv_app_congr :
    Proper (conv flags Σ ==> All2 (conv flags Σ) ==> conv flags Σ) (@TApp s).
  Proof.
  intros f f' Hf args arg' Hargs. transitivity (TApp f' args).
  - clear Hargs. induction Hf.
    + apply conv_of_red1. now constructor.
    + reflexivity.
    + now symmetry.
    + etransitivity ; eauto.
  - apply conv_app_congr_aux with (l := []). assumption.
  Qed.

End CongruenceLemmas.

(***********************************************************************)
(** * Inversion lemmas (aka injectivity of construtors). *)
(***********************************************************************)

Section InversionLemmas.
  Context {flags : red_flags} {Σ : evar_map} {s : scope}.

  (** Injectivity of [TLam]. *)
  Lemma conv_lam_inv x (ty ty' : term s) body body' :
    Σ ⊢ TLam x ty body ≡{flags} TLam x ty' body' ->
    Σ ⊢ ty ≡{flags} ty' /\ Σ ⊢ body ≡{flags} body'.
  Proof.
  intros H. apply church_rosser in H. destruct H as (t & H1 & H2).
  apply red_lam_inv in H1, H2.
  destruct H1 as (ty1' & body1' & -> & Hty1 & Hbody1).
  destruct H2 as (ty2' & body2' & Heq & Hty2 & Hbody2).
  depelim Heq. split.
  - transitivity ty1'.
    + apply conv_of_red, Hty1.
    + symmetry. apply conv_of_red, Hty2.
  - transitivity body1'.
    + apply conv_of_red, Hbody1.
    + symmetry. apply conv_of_red, Hbody2.
  Qed.

  (** Injectivity of [TProd]. *)
  Lemma conv_prod_inv x (a a' : term s) b b' :
    Σ ⊢ TProd x a b ≡{flags} TProd x a' b' ->
    Σ ⊢ a ≡{flags} a' /\ Σ ⊢ b ≡{flags} b'.
  Proof.
  intros H. apply church_rosser in H. destruct H as (t & H1 & H2).
  apply red_prod_inv in H1, H2.
  destruct H1 as (a1' & b1' & -> & Ha1 & Hb1).
  destruct H2 as (a2' & b2' & Heq & Ha2 & Hb2).
  depelim Heq. split.
  - transitivity a1'.
    + apply conv_of_red, Ha1.
    + symmetry. apply conv_of_red, Ha2.
  - transitivity b1'.
    + apply conv_of_red, Hb1.
    + symmetry. apply conv_of_red, Hb2.
  Qed.

End InversionLemmas.
