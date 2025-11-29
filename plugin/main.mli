(** This file defines the main entry-point of the plugin. *)

(** Extract, compile, and link a constant. *)
val main : opaque_access:Global.indirect_accessor -> Libnames.qualid -> unit
