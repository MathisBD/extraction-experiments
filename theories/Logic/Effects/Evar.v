From Metaprog Require Import Prelude.
From Metaprog Require Export Control.Effects.Evar Logic.WP.

(** This module defines the specification of the [evarE] effect. *)

Definition set_evar (Σ : evar_map) (ev : evar_id) (entry : evar_entry) : evar_map :=
  fun ev' => if Nat.eqb ev ev' then Some entry else Σ ev'.

(** Logical effect handler for [evarE]. *)
(* TODO: this is not entirely correct, we need to take into account that
   Rocq's evar map uses EConstr.t so evar-expansion can happen anywhere. *)
Program Definition handle_evarE : handler evarE := {|
  handler_fun _ e :=
    match e with
    (** Creating a fresh evar returns a fresh evar identifier,
        and adds the new evar to the evar-map. *)
    | FreshEvar ty => fun Φ Σ =>
      forall ev,
        Σ ev = None ->
        Φ ev (set_evar Σ ev $ mk_evar_entry ty None)
    (** Looking up an evar simply returns the (optional) evar-entry
        associated to the evar. *)
    | LookupEvar ev => fun Φ Σ =>
      Φ (Σ ev) Σ
    (** Defining an evar requires the evar to be present but not defined,
        and updates the evar-entry associated to the evar. *)
    | DefineEvar ev def => fun Φ Σ =>
      exists ty,
        Σ ev = Some (mk_evar_entry ty None) /\
        Φ tt (set_evar Σ ev $ mk_evar_entry ty (Some def))
    end
|}.
Next Obligation. intros A [ty | ev | ev def] Φ Φ' g HΦ ; firstorder. Qed.

Section WPs.
  Context {E : Type -> Type} (h : handler E) `{subhandler _ _ handle_evarE h}.

  Lemma wp_fresh_evar Φ Σ ty :
    wp h _ (fresh_evar ty) Φ Σ <->
    forall ev, Σ ev = None -> Φ ev (set_evar Σ ev $ mk_evar_entry ty None).
  Proof.
  unfold fresh_evar, trigger. rewrite wp_Vis, handle_inj. cbn. reflexivity.
  Qed.

  Lemma wp_lookup_evar Φ Σ ev :
    wp h _ (lookup_evar ev) Φ Σ <-> Φ (Σ ev) Σ.
  Proof.
  unfold lookup_evar, trigger. rewrite wp_Vis, handle_inj. cbn. reflexivity.
  Qed.

  Lemma wp_define_evar Φ Σ ev def :
    wp h _ (define_evar ev def) Φ Σ <->
    exists ty,
      Σ ev = Some (mk_evar_entry ty None) /\
      Φ tt (set_evar Σ ev $ mk_evar_entry ty $ Some def).
  Proof.
  unfold define_evar, trigger. rewrite wp_Vis, handle_inj. cbn. reflexivity.
  Qed.

End WPs.