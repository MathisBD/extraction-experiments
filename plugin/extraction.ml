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
