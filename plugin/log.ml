(** Printing utilities for Rocq. *)

(** [Log.printf] is a standard [printf] function, except it automatically adds a newline
      at the end. *)
let printf ?(loc : Loc.t option) fmt =
  Format.ksprintf (fun res -> Feedback.msg_notice ?loc (Pp.str res)) fmt

(** Same as [Log.printf] except it generates an error instead. *)
let error ?(loc : Loc.t option) fmt =
  Format.ksprintf (fun res -> CErrors.user_err ?loc (Pp.str res)) fmt

(** Print an [EConstr.t] to a string. *)
let show_econstr env sigma t : string =
  Pp.string_of_ppcmds @@ Printer.pr_econstr_env env sigma t

(** Print the raw representation of a [Constr.t] to a string. *)
let show_constr_raw t : string =
  Pp.string_of_ppcmds @@ Constr.debug_print t