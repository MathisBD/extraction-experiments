From Metaprog Require Import Prelude.
From Metaprog Require Export Data.Term Extraction.Basic.

(** This module specifies how to extract terms and related types.
    It makes heavy use of OCaml constants and functions defined
    in the plugin (file "plugin/extraction.ml"). *)

(** We extract scopes to [int]. In the future we should
    mark [scope] as [Ghost] to have it erased entirely by extraction. *)
Extract Inductive scope => "int" [ "0" "Stdlib.Int.succ" ]
  "MyPlugin.Extraction.nat_elim".

Extract Inductive index => "MyPlugin.Extraction.index"
  [ "MyPlugin.Extraction.I0" "MyPlugin.Extraction.IS" ].

Extract Inductive term => "MyPlugin.Extraction.term"
  [ "MyPlugin.Extraction.TType"
    "MyPlugin.Extraction.TVar"
    "MyPlugin.Extraction.TLam"
    "MyPlugin.Extraction.TProd"
    "MyPlugin.Extraction.TApp"
    "MyPlugin.Extraction.TEvar" ].
