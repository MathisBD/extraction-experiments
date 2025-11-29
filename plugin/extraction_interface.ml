(** This file defines the interface that extracted code uses. *)

(** Effect handler for [Print]. *)
let ocaml_handle_print (str : Pstring.t) : unit =
  Log.printf "%s" (Pstring.to_string str)
