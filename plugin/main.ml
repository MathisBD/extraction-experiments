
module Log = struct
  (** [Log.printf] is a standard [printf] function, except it automatically adds a newline
      at the end. *)
  let printf fmt =
    Format.ksprintf (fun res -> Feedback.msg_notice (Pp.str res)) fmt

  (** Print an [EConstr.t] to a string. *)
  let show_econstr env sigma t : string =
    Pp.string_of_ppcmds @@ Printer.pr_econstr_env env sigma t
end

let main ~opaque_access (ref : Libnames.qualid) : unit =
  let env = Global.env () in
  let _evm = Evd.from_env env in
  Dynlink.loadfile_private "theories/hello.cmxs";
  Log.printf "loaded file"
  (*Extract_env.full_extraction ~opaque_access (Some file) [ ref ];
  Log.printf "Extracted to file \"%s\"" file*)