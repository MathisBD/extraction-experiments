(** This file defines the interface that extracted code uses. *)

(*******************************************************************)
(** * Utility functions. *)
(*******************************************************************)

(** Substraction function on [nat] for extraction.
    Substraction on [nat] is _not_ the same as substraction on [int]. *)
let nat_sub (x : int) (y : int) : int =
  Stdlib.Int.max 0 (x - y)

(** Pattern matching function for [nat] extraction. *)
let nat_elim (fO : unit -> 'a) (fS : int -> 'a) (n : int) : 'a =
  if n = 0 then fO () else fS (n - 1)

(*******************************************************************)
(** * Persistent vectors. *)
(*******************************************************************)

(** Persistent vectors (aka dynamic arrays).
    We use an interface to be able to swap different implementations as needed. *)
module Vec : sig
  type 'a t

  (** Create an empty vector. *)
  val empty : unit -> 'a t

  (** Add an element to a vector. *)
  val add : 'a t -> 'a -> 'a t

  (** Remove the last element of a vector. *)
  val pop : 'a t -> 'a t * 'a

  (** Get the element at a specific position in a vector. *)
  val get : 'a t -> int -> 'a

  (** Set the element at a specific position in a vector. *)
  val set : 'a t -> int -> 'a -> 'a t

  (** Get the length of a vector. *)
  val length : 'a t -> int
end = struct
  type 'a t = 'a Pvec.t
  let empty () = Pvec.empty ()
  let add xs x = Pvec.append x xs
  let pop xs = let (x, xs) = Option.get (Pvec.pop xs) in (xs, x)
  let get xs i = Option.get (Pvec.get i xs)
  let set xs i x = Option.get (Pvec.set i x xs)
  let length xs = Pvec.length xs
end

(*******************************************************************)
(** * Terms. *)
(*******************************************************************)

type scope = int

(** Scoped de Bruijn indices. *)
type index =
| I0 of scope
| IS of scope * index

(** Renamings. *)
(*type ren = index -> index*)

type evar_id = int

type term =
| TType
| TVar of index
| TLam of term * term
| TProd of term * term
| TApp of term * term list
| TEvar of evar_id

(** [idx] lives in scope [s]. *)
let rec index_of_int (s : scope) (idx : int) : index =
  if idx <= 0 then I0 s
  else IS (s - 1, index_of_int (s - 1) (idx - 1))

(** Check if a Rocq sort is [Type@{u}] for some universe [u]. *)
let is_type evm (s : EConstr.ESorts.t) : bool =
  match EConstr.ESorts.kind evm s with
  | Type _ -> true
  | _ -> false

let rec term_of_econstr (evm : Evd.evar_map) (s : scope) (c : EConstr.t) : term =
  match EConstr.kind evm c with
  | Sort sort when is_type evm sort -> TType
  | Rel idx -> TVar (index_of_int s idx)
  | Lambda (x, ty, body) ->
    let ty = term_of_econstr evm s ty in
    let body = term_of_econstr evm (s + 1) body in
    TLam (ty, body)
  | Prod (x, a, b) ->
    let a = term_of_econstr evm s a in
    let b = term_of_econstr evm (s + 1) b in
    TProd (a, b)
  | App (f, args) ->
    let f = term_of_econstr evm s f in
    let args = List.map (term_of_econstr evm s) @@ Array.to_list args in
    TApp (f, args)
  | _ ->
    Log.error "term_of_econstr: unsupported term %s" (Log.show_econstr (Global.env ()) evm c)

let rec int_of_index (i : index) : int =
  match i with
  | I0 _ -> 0
  | IS (_, i) -> 1 + int_of_index i

(** Map a function which modifies the evar-map over a list. *)
let rec map_evm (f : Evd.evar_map -> 'a -> Evd.evar_map * 'b)
  (evm : Evd.evar_map) (xs : 'a list) : Evd.evar_map * 'b list =
  match xs with
  | [] -> evm, []
  | x :: xs ->
    let evm, y = f evm x in
    let evm, ys = map_evm f evm xs in
    evm, y :: ys

let rec econstr_of_term evm (t : term) : Evd.evar_map * EConstr.t =
  match t with
  | TType -> Evarutil.new_Type evm
  | TVar idx -> (evm, EConstr.mkRel (int_of_index idx))
  | TLam (ty, body) ->
    let evm, ty = econstr_of_term evm ty in
    let evm, body = econstr_of_term evm body in
    let annot = EConstr.annotR @@ Names.Name.mk_name @@ Names.Id.of_string_soft "x" in
    (evm, EConstr.mkLambda (annot, ty, body))
  | TProd (a, b) ->
    let evm, a = econstr_of_term evm a in
    let evm, b = econstr_of_term evm b in
    let annot = EConstr.annotR @@ Names.Name.mk_name @@ Names.Id.of_string_soft "x" in
    (evm, EConstr.mkProd (annot, a, b))
  | TApp (f, args) ->
    let evm, f = econstr_of_term evm f in
    let evm, args = map_evm econstr_of_term evm args in
    (evm, EConstr.mkApp (f, Array.of_list args))
  | TEvar ev -> (evm, EConstr.mkEvar (Evar.unsafe_of_int ev, SList.empty))

(*******************************************************************)
(** * Effect handlers. *)
(*******************************************************************)

(** Effect handler for [Print]. *)
let handle_Print (str : Pstring.t) : unit =
  Log.printf "%s" (Pstring.to_string str)

(** Effect handler for [Fail]. *)
let handle_Fail (str : Pstring.t) : 'a =
  Log.error "%s" (Pstring.to_string str)

let handle_FreshEvar (evm : Evd.evar_map) (ty : term) : Evd.evar_map * evar_id =
  let evm, ty = econstr_of_term evm ty in
  let evm, ev = Evarutil.new_evar (Global.env ()) evm ty in
  let ev_id, ev_args = EConstr.destEvar evm ev in
  if SList.is_empty ev_args then
    (Log.printf "added evar %d with type %s" (Evar.repr ev_id) (Log.show_econstr_raw evm ty) ;
    (evm, Evar.repr ev_id))
  else
    Log.error "handle_FreshEvar: created evar with non-empty suspended substitution"

(*let handle_get_definition (env : Environ.env) (str : Pstring.t) : term =
  let kname = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string @@ Pstring.to_string str) in
  let kbody = Environ.lookup_constant kname env in
  match kbody.const_body with
  | Def d -> term_of_constr 0 d
  | _ -> Log.error "Constant %s has no body" (Pstring.to_string str)*)