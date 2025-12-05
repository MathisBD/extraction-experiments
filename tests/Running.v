From Stdlib Require Strings.PrimString.
From Metaprog Require Import Hitree RunHitree.

Import PrimString.PStringNotations.
Open Scope pstring_scope.

(*******************************************************************)
(** * Concrete effect. *)
(*******************************************************************)

(** A concrete effect. *)
Inductive E (A : Type) : Type :=
| E_printE (e : printE A)
| E_failE (e : failE A)
| E_iterE (e : iterE E A)
| E_recE (e : recE E A).

Arguments E_printE {A}.
Arguments E_failE {A}.
Arguments E_iterE {A}.
Arguments E_recE {A}.

Instance subeffect_printE : printE -< E := { inj_effect := @E_printE }.
Instance subeffect_failE : failE -< E := { inj_effect := @E_failE }.
Instance subeffect_iterE : iterE E -< E := { inj_effect := @E_iterE }.
Instance subeffect_recE : recE E -< E := { inj_effect := @E_recE }.

(** Run an hitree computation with effect [E]. *)
Fixpoint ocaml_run_hitree {A} (n : fuel) (fs : Vec.t (entry E)) (t : hitree E A) : A :=
  match n with NoFuel => ocaml_handle_Fail _ "ocaml_run_hitree: out of fuel (should not happen)" | OneMoreFuel n =>
  match t with
  (* Ret. *)
  | Ret x => x
  (* Bind. *)
  | Bind t f =>
    let x := ocaml_run_hitree n fs t in
    ocaml_run_hitree n fs (f x)
  (* Print effect. *)
  | Vis (E_printE e) =>
    match e with
    | Print s => ocaml_handle_Print s
    end
  (* Failure effect. *)
  | Vis (E_failE e) =>
    match e with
    | Fail s => ocaml_handle_Fail _ s
    end
  (* Iteration effect. *)
  | Vis (E_iterE e) =>
    match e with
    | Iter init step =>
      let ab := ocaml_run_hitree n fs (step init) in
      match ab with
      | Continue a => ocaml_run_hitree n fs (iter a step)
      | Break b => b
      end
    end
  (* Recursion effect. *)
  | Vis (E_recE e) =>
    match e with
    (* MkFix: add the function to the environment and run the body. *)
    | MkFix F a =>
      let x := Vec.length fs in
      let ent := mk_entry E _ _ (F x) in
      ocaml_run_hitree n (Vec.add fs ent) (F x a)
    (* Call: Lookup the function in the environment. *)
    | Call x a =>
      let e := Vec.get fs x in
      ocaml_run_hitree n fs (ocaml_obj_magic (entry_fun e (ocaml_obj_magic a)))
    end
  end
  end.

(*******************************************************************)
(** * Testing. *)
(*******************************************************************)

Definition prg : hitree E unit :=
  (for i = 1 to 5 do print "hello") >>
  print "done".

Definition prg_rec : hitree E unit :=
  letrec loop i :=
    if Nat.ltb i 5 then print "hello" >> loop (i + 1)
    else Ret tt
  in
  loop 1.

Definition test : unit :=
  ocaml_run_hitree NoFuel (Vec.empty tt) prg_rec.

Test test.