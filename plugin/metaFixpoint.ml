

type vernac_meta_fixpoint = {
  name : Names.lident ;
  univs : Constrexpr.universe_decl_expr option ;
  binders : Constrexpr.local_binder_expr list ;
  rtype : Constrexpr.constr_expr ;
  body : Constrexpr.constr_expr
}

(** Warning raised when a meta fixpoint is not truly recursive. *)
let warn_non_recursive =
  let open Pp in
  CWarnings.create ~name:"non-recursive-meta" ~category:CWarnings.CoreCategories.fixpoints
    (fun () -> strbrk "Not a truly recursive MetaFixpoint.")

(** Build the functional corresponding to a meta fixpoint.
    The functional is the term that we use as argument to [fixX] combinator.

    The term returned by [interp_mutual_fixpoint] may still contain unresolved evars. *)
let interp_mutual_fixpoint (env : Environ.env) (decl : vernac_meta_fixpoint) : Evd.evar_map * EConstr.t =
  (* Interpret the type of the fixpoint parameter, allowing for unresolved evars. *)
  let sigma, univs = Constrintern.interp_univ_decl_opt env decl.univs in
  let sigma, (impls, ((env, args_ctx), ctx_implicits, _)) = Constrintern.interp_context_evars env sigma decl.binders in
  let sigma, (rtype, rtype_implicits) = Constrintern.interp_type_evars_impls ~impls env sigma decl.rtype in
  let fix_type = Evarutil.nf_evar sigma (EConstr.it_mkProd_or_LetIn rtype args_ctx) in

  (* Make a named declaration for the fixpoint parameter. *)
  let annot = Context.make_annot decl.name.v (Retyping.relevance_of_type env sigma rtype) in
  let rec_decl = Context.Named.Declaration.LocalAssum (annot, fix_type) in
  let implicits = ctx_implicits @ rtype_implicits in

  (* Interpret the body in an environment which contains the fixpoint parameter and the arguments. *)
  let impls = Constrintern.compute_internalization_env env sigma Recursive [ decl.name.v ] [ fix_type ] [ implicits ] in
  let env_body = env |> EConstr.push_named rec_decl |> EConstr.push_rel_context args_ctx in
  let sigma, body = Constrintern.interp_casted_constr_evars env_body sigma ~impls decl.body rtype in

  (* Check the fixpoint is truly recursive, i.e. check the body contains the fixpoint parameter. *)
  let is_recursive = Termops.occur_var env sigma decl.name.v body in
  if not is_recursive then warn_non_recursive ();

  (* Build the functional, i.e. the function which implements one recursion step. *)
  let functional = EConstr.mkNamedLambda sigma annot fix_type @@ EConstr.it_mkLambda_or_LetIn body args_ctx in
  sigma, functional

let define_meta_fixpoint (decl : vernac_meta_fixpoint) : unit =
  let env = Global.env () in
  let sigma, functional = interp_mutual_fixpoint env decl in
  Log.printf "Functional: %s" (Log.show_econstr env sigma functional);
