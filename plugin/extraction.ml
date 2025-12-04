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
type ren = index -> index

type evar_id = int

type term =
| TType of scope
| TVar of scope * index
| TLam of scope * term * term
| TProd of scope * term * term
| TApp of scope * term * term list
| TEvar of scope * evar_id
| TRen of scope * scope * ren * term

(** [idx] lives in scope [s]. *)
let rec index_of_int (s : scope) (idx : int) : index =
  if idx <= 0 then I0 s
  else IS (s - 1, index_of_int (s - 1) (idx - 1))

(** [c] lives in scope [s]. *)
let rec term_of_constr (s : scope) (c : Constr.t) : term =
  match Constr.kind c with
  | Rel idx -> TVar (s, index_of_int s idx)
  | Sort (Type _) -> TType s
  | Lambda (x, ty, body) ->
    let ty = term_of_constr s ty in
    let body = term_of_constr (s + 1) body in
    TLam (s, ty, body)
  | Prod (x, a, b) ->
    let a = term_of_constr s a in
    let b = term_of_constr (s + 1) b in
    TProd (s, a, b)
  | App (f, args) ->
    let f = term_of_constr s f in
    let args = List.map (term_of_constr s) @@ Array.to_list args in
    TApp (s, f, args)
  | _ ->
    Log.error "term_of_constr: unsupported term %s" (Log.show_constr_raw c)

(*******************************************************************)
(** * Effect handlers. *)
(*******************************************************************)

(** Effect handler for [Print]. *)
let handle_Print (str : Pstring.t) : unit =
  Log.printf "%s" (Pstring.to_string str)

(** Effect handler for [Fail]. *)
let handle_Fail (str : Pstring.t) : 'a =
  Log.error "%s" (Pstring.to_string str)

let handle_get_definition (env : Environ.env) (str : Pstring.t) : term =
  let kname = Smartlocate.global_constant_with_alias (Libnames.qualid_of_string @@ Pstring.to_string str) in
  let kbody = Environ.lookup_constant kname env in
  match kbody.const_body with
  | Def d -> term_of_constr 0 d
  | _ -> Log.error "Constant %s has no body" (Pstring.to_string str)