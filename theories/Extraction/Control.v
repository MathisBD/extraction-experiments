From Metaprog Require Import Prelude Data.Term Extraction.Basic Extraction.Data.
From Metaprog.Control Require Import Meta Command Effects.All.

(** This module specifies how to extract the meta-programming monad
    and effects to OCaml. *)

Parameter ocaml_evar_map : Type.
Extract Inlined Constant ocaml_evar_map => "Evd.Evar_map".

Parameter ocaml_initial_evar_map : unit -> ocaml_evar_map.
Extract Inlined Constant ocaml_initial_evar_map => "(fun _ -> Evd.from_env (Global.env ()))".

(*******************************************************************)
(** * Effect handlers. *)
(*******************************************************************)

(** The effect handler for [Print] in OCaml. *)
Parameter ocaml_handle_Print : string -> unit.
Extract Inlined Constant ocaml_handle_Print => "MyPlugin.Extraction.handle_Print".

(** The effect handler for [Fail] in OCaml. *)
Parameter ocaml_handle_Fail : forall A, string -> A.
Extract Inlined Constant ocaml_handle_Fail => "MyPlugin.Extraction.handle_Fail".

Parameter ocaml_handle_FreshEvar : ocaml_evar_map -> term ∅ -> ocaml_evar_map * evar_id.
Extract Inlined Constant ocaml_handle_FreshEvar => "MyPlugin.Extraction.handle_FreshEvar".

(*******************************************************************)
(** * Running metaprograms with the [commandE] effect. *)
(*******************************************************************)

(** Never ending fuel. *)
Inductive fuel :=
| NoFuel
| OneMoreFuel (f : fuel).

(** We extract [fuel] to [unit]: there is only one fuel [n]
    and it is always of the form [n = OneMoreFuel n].
    This way we can write functions using fuel in Rocq and they never run
    out of fuel in OCaml! *)
Extract Inductive fuel => "unit" [ "()" "(fun _ -> ())" ] "(fun f0 f1 _ -> f1 ())".

(** Entry for a recursive function. *)
Record fun_entry (E : Type -> Type) := mk_entry {
  entry_dom : Type ;
  entry_codom : entry_dom -> Type ;
  entry_fun : forall a : entry_dom, meta E (entry_codom a)
}.

Arguments entry_dom {E}.
Arguments entry_codom {E}.
Arguments entry_fun {E}.

(** TODO: this might need to be tail-recursive to avoid stack overflow. *)
Fixpoint run_command_rec {A} (n : fuel) (fs : Vec.t (fun_entry commandE))
  (evm : ocaml_evar_map) (t : meta commandE A) : ocaml_evar_map * A :=
  match n with NoFuel => ocaml_handle_Fail _ "run_command_rec: out of fuel (should not happen)" | OneMoreFuel n =>
  match t with
  (* Return. *)
  | Return x => (evm, x)
  (* Bind. *)
  | Bind t f =>
    let (evm, x) := run_command_rec n fs evm t in
    run_command_rec n fs evm (f x)
  (* Print effect. *)
  | Vis (command_print e) =>
    match e with
    | Print s => (evm, ocaml_handle_Print s)
    end
  (* Failure effect. *)
  | Vis (command_fail e) =>
    match e with
    | Fail s => (evm, ocaml_handle_Fail _ s)
    end
  (* Iteration effect. *)
  | Vis (command_iter e) =>
    match e with
    | Iter init step =>
      let (evm, ab) := run_command_rec n fs evm (step init) in
      match ab with
      | Continue a => run_command_rec n fs evm (iter a step)
      | Break b => (evm, b)
      end
    end
  (* Recursion effect. *)
  | Vis (command_rec e) =>
    match e with
    (* MkFix: add the function to the environment and run the body. *)
    | @MkFix _ A B F a =>
      let k := Key A B (Vec.length fs) in
      let ent := mk_entry commandE A B (F k) in
      run_command_rec n (Vec.add fs ent) evm (F k a)
    (* Call: Lookup the function in the environment.
       This will crash if the function in the environment has the incorrect type. *)
    | Call (Key _ _ x) a =>
      let e := Vec.get fs x in
      run_command_rec n fs evm (ocaml_obj_magic (entry_fun e (ocaml_obj_magic a)))
    end
  | Vis (command_evar e) =>
    match e with
    | FreshEvar ty => ocaml_handle_Fail _ "todo: FreshEvar"
    | LookupEvar ev => ocaml_handle_Fail _ "todo: LookupEvar"
    | DefineEvar ev def => ocaml_handle_Fail _ "todo: DefineEvar"
    end
  end
  end.

(** Run a command at toplevel. *)
Definition run_command (t : meta commandE unit) : unit :=
  let evm := ocaml_initial_evar_map tt in
  snd (run_command_rec NoFuel (Vec.empty tt) evm t).