open Extraction_plugin
open File_utils

(** Effect handler for [Print]. *)
let ocaml_handle_print (str : Pstring.t) : unit =
  Log.printf "%s" (Pstring.to_string str)


let extract ~opaque_access ~dir (ref : Libnames.qualid) : unit =
  let file_name = dir </> "extracted.ml" in
  Extract_env.full_extraction ~opaque_access (Some file_name) [ ref ]

let main ~opaque_access (ref : Libnames.qualid) : unit =
  let dir = mk_tmp_dir "metaprog" in
  extract ~opaque_access ~dir ref

  (*Dynlink.loadfile_private "theories/hello.cmxs";
  Log.printf "loaded file"*)
