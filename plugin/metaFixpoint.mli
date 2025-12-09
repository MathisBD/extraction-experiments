(** This module implements the [MetaFixpoint] command. *)

(** [vernac_meta_fixpoint] is what we get after parsing a meta fixpoint definition. *)
type vernac_meta_fixpoint = {
  name : Names.lident ;
  univs : Constrexpr.universe_decl_expr option ;
  binders : Constrexpr.local_binder_expr list ;
  rtype : Constrexpr.constr_expr ;
  body : Constrexpr.constr_expr
}

(** Define a fixpoint in the [meta] monad. *)
val define_meta_fixpoint : vernac_meta_fixpoint -> unit