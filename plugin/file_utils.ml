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
  let rand = Random.State.(bits (make_self_init ()) land 0xFFFFFF) in
  let name =
    Filename.get_temp_dir_name () </>
    name </>
    (Printf.sprintf "%02dh%02dm%02ds_%06x" time.tm_hour time.tm_min time.tm_sec rand)
  in
  (* TODO: try several times with different random numbers. *)
  mk_dir ~allow_exists:false ~perms:0o755 name;
  name