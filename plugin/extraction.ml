(** This file defines the interface that extracted code uses. *)

(** Substraction function on [nat] for extraction.
    Substraction on [nat] is _not_ the same as substraction on [int]. *)
let nat_sub (x : int) (y : int) : int =
  Stdlib.Int.max 0 (x - y)

(** Pattern matching function for [nat] extraction. *)
let nat_elim (fO : unit -> 'a) (fS : int -> 'a) (n : int) : 'a =
  if n = 0 then fO () else fS (n - 1)

(** Effect handler for [Print]. *)
let handle_Print (str : Pstring.t) : unit =
  Log.printf "%s" (Pstring.to_string str)

(** Effect handler for [Fail]. *)
let handle_Fail (str : Pstring.t) : 'a =
  Log.error "%s" (Pstring.to_string str)

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

