open Unix

let (</>) = Filename.concat

let rec mk_dir ?(allow_exists = true) ~(perms:file_perm) (name : string) : unit =
  try Unix.mkdir name perms with
  (* The directory already exists. *)
  | Unix_error (EEXIST, _, _) ->
    if allow_exists then () else
    Log.error "Plugin error: failed to create directory %s" name
  (* We need to create the parent directory first. *)
  | Unix_error (ENOENT, _, _) ->
    let parent = Filename.dirname name in
    mk_dir ~allow_exists ~perms parent;
    Unix.mkdir name perms
  (* Error. *)
  | _ -> Log.error "Plugin error: failed to create directory %s" name

let mk_tmp_dir (name : string) : string =
  let time = localtime (time ()) in
  let cmd =
    Printf.sprintf "mktemp -d --tmpdir %s_%02dh%02dm%02ds_XXXXXX"
      name time.tm_hour time.tm_min time.tm_sec
  in
  let chan = Unix.open_process_in cmd in
  let name = input_line chan in
  match Unix.close_process_in chan with
  | Unix.WEXITED 0 -> name
  | _ -> Log.error "Plugin error: failed to create temporary directory with base name %s" name

let read_file (name : string) : string =
  let chan = In_channel.open_text name in
  let contents = In_channel.input_all chan in
  In_channel.close chan;
  contents