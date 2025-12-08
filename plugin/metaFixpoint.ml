

type vernac_meta_fixpoint = {
  name : Names.lident ;
  univs : Constrexpr.universe_decl_expr option ;
  binders : Constrexpr.local_binder_expr list ;
  rtype : Constrexpr.constr_expr ;
  body : Constrexpr.constr_expr
}

(** Resolve a reference [ref] registered in a Rocq file with [Register _ as ref]. *)
let resolve (ref : string) : Names.GlobRef.t Lazy.t = lazy (Rocqlib.lib_ref ref)

let rocq_fix1 = resolve "metaprog.control.effects.rec.fix1"
let rocq_fix2 = resolve "metaprog.control.effects.rec.fix2"
let rocq_fix3 = resolve "metaprog.control.effects.rec.fix3"
let rocq_fix4 = resolve "metaprog.control.effects.rec.fix4"
let rocq_fix5 = resolve "metaprog.control.effects.rec.fix5"

(** Create a fresh [Type] instance. *)
let fresh_type env sigma : Evd.evar_map * EConstr.t =
  let sigma, level = Evd.new_univ_level_variable Evd.univ_flexible sigma in
  (sigma, EConstr.mkType @@ Univ.Universe.make level)

(** Create a fresh evar. *)
let fresh_evar env sigma : Evd.evar_map * EConstr.t =
  let sigma, t = fresh_type env sigma in
  let sigma, ty = Evarutil.new_evar env sigma t in
  Evarutil.new_evar env sigma ty

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

(** Pick the correct fixpoint combinator depending on the number of arguments. *)
let pick_fix_combinator (fname : Names.Id.t) (n_args : int) : Names.GlobRef.t =
  if n_args = 0 then
    Log.error "Meta fixpoint '%s' must take at least one parameter." (Names.Id.to_string fname)
  else if n_args = 1 then Lazy.force rocq_fix1
  else if n_args = 2 then Lazy.force rocq_fix2
  else if n_args = 3 then Lazy.force rocq_fix3
  else if n_args = 4 then Lazy.force rocq_fix4
  else if n_args = 5 then Lazy.force rocq_fix5
  else Log.error "Meta fixpoint '%s' takes too many arguments (%d)" (Names.Id.to_string fname) n_args

(** Build the function corresponding to a meta fixpoint. *)
let interp_mutual_fixpoint env (decl : vernac_meta_fixpoint) : Evd.evar_map * EConstr.t =
  (* Interpret the type of the fixpoint parameter, allowing for unresolved evars. *)
  let sigma, univs = Constrintern.interp_univ_decl_opt env decl.univs in
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
  let n_args = List.length decl.binders in
  let rocq_fix = pick_fix_combinator decl.name.v n_args in
  (* We need 1 evar for [E : Type -> Type], 1 evar for [recE E -< e],
     1 evar for the type of each argument, and 1 evar for the return type. *)
  let sigma, ev = fresh_evar env sigma in
  let sigma, ev_inst = fresh_evar env sigma in
  let sigma, evars = fresh_evars env sigma (n_args + 1) in
  let sigma, combinator = EConstr.fresh_global env sigma rocq_fix in
  let func = EConstr.mkApp (combinator, Array.of_list (ev :: ev_inst :: evars @ [ functional ])) in

  (* Type-check the resulting term. *)
  let sigma = Typing.check env sigma func fix_type in
  Log.printf "func after typecheck: %s" (Log.show_econstr env sigma func);

  (* Instantiate the instance evar. *)
  let sigma, inst = EConstr.fresh_global env sigma (Lazy.force @@ resolve "metaprog.e_sub") in
  let sigma = Evd.define (fst @@ EConstr.destEvar sigma ev_inst) inst sigma in
  let sigma = Typing.check env sigma func fix_type in
  Log.printf "func after instantiation: %s" (Log.show_econstr env sigma func);

  (* Instantiate evars and check all are resolved. *)
  (*let sigma = Typeclasses.resolve_typeclasses env sigma in*)
  let sigma = Evarconv.solve_unif_constraints_with_heuristics env sigma in
  let sigma = Evd.minimize_universes sigma in
  let sigma = Pretyping.(solve_remaining_evars all_no_fail_flags env sigma) in
  Pretyping.check_evars_are_solved ~program_mode:false env sigma;

  (* Finally check the fixpoint is truly recursive, i.e. check the body contains the fixpoint parameter. *)
  let is_recursive = Termops.occur_var env_body sigma decl.name.v body in
  if not is_recursive then warn_non_recursive ();

  sigma, func

let define_meta_fixpoint (decl : vernac_meta_fixpoint) : unit =
  let env = Global.env () in
  (*match Typeclasses.instances (Lazy.force @@ resolve "metaprog.meta.subeffect") with
  | None -> Log.printf "no instance found"
  | Some insts ->
    Log.printf "found %d intance(s)" (List.length insts);
    List.iter (fun inst ->
      Log.printf "class=%s ; impl=%s"
        (Pp.string_of_ppcmds @@ Printer.pr_global inst.Typeclasses.is_class)
        (Pp.string_of_ppcmds @@ Printer.pr_global inst.Typeclasses.is_impl))
        insts*)

  let sigma, func = interp_mutual_fixpoint env decl in
  Log.printf "Function: %s" (Log.show_econstr env sigma func)
