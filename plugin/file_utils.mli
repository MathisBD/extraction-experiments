(** This file defines utilities to manipulate files and directories. *)

(** Concatenate file paths. *)
val (</>) : string -> string -> string

(** [mk_dir ?allow_exists perms dir] creates directory [dir] with permissions [perm],
    taking care to create any parent directories as needed.
    - [allow_exists]: if [true], do nothing if the directory already exists.
      Defaults to [true]. *)
val mk_dir : ?allow_exists:bool -> perms:Unix.file_perm -> string -> unit

(** [mk_tmp_dir name] creates a temporary directory with
    name [${tmp}/${name}/${time}_${rand}] where:
    - [tmp] is the temporary directory (e.g. /tmp on linux).
    - [time] is the current time in format [HHMMSS].
    - [rand] is a random number to ensure uniqueness.

    It returns the name of the created directory. *)
val mk_tmp_dir : string -> string