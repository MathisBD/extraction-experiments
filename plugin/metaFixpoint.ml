

type vernac_meta_fixpoint = {
  name : Names.lident ;
  univs : Constrexpr.universe_decl_expr option ;
  binders : Constrexpr.local_binder_expr list ;
  rtype : Constrexpr.constr_expr ;
  body : Constrexpr.constr_expr
}

(** Create a fresh [Type] instance. *)
let fresh_type env sigma : Evd.evar_map * EConstr.t =
  let sigma, level = Evd.new_univ_level_variable Evd.univ_flexible sigma in
  (sigma, EConstr.mkType @@ Univ.Universe.make level)

(** Create a fresh evar. The evar can be solved using typeclass resolution,
    but its type cannot. We might change this in the future. *)
let fresh_evar env sigma : Evd.evar_map * EConstr.t =
  let sigma, t = fresh_type env sigma in
  let sigma, ty = Evarutil.new_evar env sigma t in
  Evarutil.new_evar ~typeclass_candidate:true env sigma ty

(** Create [n] fresh evars. *)
let rec fresh_evars env sigma n : Evd.evar_map * EConstr.t list =
  if n <= 0 then sigma, []
  else
    let sigma, ev = fresh_evar env sigma in
    let sigma, evs = fresh_evars env sigma (n-1) in
    sigma, (ev :: evs)

(** Warning raised when a meta fixpoint is not truly recursive. *)
let warn_non_recursive =
  let open Pp in
  CWarnings.create ~name:"non-recursive-meta" ~category:CWarnings.CoreCategories.fixpoints
    (fun () -> strbrk "Not a truly recursive MetaFixpoint.")

(** Pick the correct fixpoint combinator depending on the number of parameters. *)
let pick_fix_combinator (fname : Names.Id.t) (n_params : int) : Names.GlobRef.t =
  if n_params = 0 then
    Log.error "Meta fixpoint '%s' must take at least one parameter." (Names.Id.to_string fname)
  else if n_params = 1 then Rocqlib.lib_ref "metaprog.control.effects.rec.fix1"
  else if n_params = 2 then Rocqlib.lib_ref "metaprog.control.effects.rec.fix2"
  else if n_params = 3 then Rocqlib.lib_ref "metaprog.control.effects.rec.fix3"
  else if n_params = 4 then Rocqlib.lib_ref "metaprog.control.effects.rec.fix4"
  else if n_params = 5 then Rocqlib.lib_ref "metaprog.control.effects.rec.fix5"
  else Log.error "Meta fixpoint '%s' takes too many arguments (%d)" (Names.Id.to_string fname) n_params

(** Count the number of parameters of the function, given its type. *)
let count_parameters env sigma (fix_type : EConstr.t) : int =
  (* Some parameters might be in the return type, e.g. if the return type is [A -> meta E B].
     To count correctly, we used reduction on the fixpoint type. *)
  let ctx, _ = Reductionops.whd_decompose_prod env sigma fix_type in
  List.length ctx

(** Build and define the function corresponding to a meta fixpoint. *)
let define_meta_fixpoint  (decl : vernac_meta_fixpoint) : unit =
  let env = Global.env () in

  (* Interpret the type of the fixpoint parameter, allowing for unresolved evars. *)
  let sigma, udecl = Constrintern.interp_univ_decl_opt env decl.univs in
  let sigma, (impls, ((env_args, args_ctx), ctx_implicits, _)) = Constrintern.interp_context_evars env sigma decl.binders in
  let sigma, (rtype, rtype_implicits) = Constrintern.interp_type_evars_impls ~impls env_args sigma decl.rtype in
  let fix_type = Evarutil.nf_evar sigma (EConstr.it_mkProd_or_LetIn rtype args_ctx) in
  let fix_relevance = Retyping.relevance_of_type env_args sigma rtype in

  (* Make a named declaration for the fixpoint parameter. *)
  let annot = Context.make_annot decl.name.v fix_relevance in
  let rec_decl = Context.Named.Declaration.LocalAssum (annot, fix_type) in
  let implicits = ctx_implicits @ rtype_implicits in

  (* Interpret the body in an environment which contains the fixpoint parameter and the arguments. *)
  let impls = Constrintern.compute_internalization_env env sigma Recursive [ decl.name.v ] [ fix_type ] [ implicits ] in
  let env_body = env |> EConstr.push_named rec_decl |> EConstr.push_rel_context args_ctx in
  let sigma, body = Constrintern.interp_casted_constr_evars env_body sigma ~impls decl.body rtype in

  (* Build the functional, i.e. the function which implements one recursion step. *)
  let functional = EConstr.mkNamedLambda sigma annot fix_type @@ EConstr.it_mkLambda_or_LetIn body args_ctx in

  (* Apply the fixpoint combinator the functional. *)
  let n_params = count_parameters env sigma fix_type in
  let rocq_fix = pick_fix_combinator decl.name.v n_params in
  (* We need 1 evar for [E : Type -> Type], 1 evar for [recE E -< E],
     1 evar for the type of each argument, and 1 evar for the return type. *)
  let sigma, evars = fresh_evars env sigma (n_params + 3) in
  let sigma, combinator = EConstr.fresh_global env sigma rocq_fix in
  let func = EConstr.mkApp (combinator, Array.of_list (evars @ [ functional ])) in

  (* Type-check the resulting term, using typeclass resolution. *)
  let sigma = Typing.check env sigma func fix_type in
  let sigma = Typeclasses.resolve_typeclasses env sigma in
  (*Log.printf "func after typecheck: %s" (Log.show_econstr env sigma func);*)
  Pretyping.check_evars_are_solved ~program_mode:false env sigma;

  (* Check the fixpoint is truly recursive, i.e. check the body contains the fixpoint parameter. *)
  let is_recursive = Termops.occur_var env_body sigma decl.name.v body in
  if not is_recursive then warn_non_recursive ();

  (* Add the function to the global environment. *)
  let info =
    Declare.Info.make ~kind:(Decls.IsDefinition Decls.Definition) ~udecl
      ~scope:(Locality.Global Locality.ImportDefaultBehavior) ()
  in
  let _ =
    Declare.declare_definition ~info
      ~cinfo:(Declare.CInfo.make ~name:decl.name.v ~typ:(Some fix_type) ~impargs:implicits ())
      ~opaque:false ~body:func sigma
  in
  ()