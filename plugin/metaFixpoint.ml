

type vernac_meta_fixpoint = {
  name : Names.lident ;
  univs : Constrexpr.universe_decl_expr option ;
  binders : Constrexpr.local_binder_expr list ;
  rtype : Constrexpr.constr_expr ;
  body : Constrexpr.constr_expr
}

let define_meta_fixpoint (decl : vernac_meta_fixpoint) : unit =
  let env = Global.env () in
  let _sigma = Evd.from_env env in
  Log.printf "define_meta_fixpoint %s" (Names.Id.to_string decl.name.v)