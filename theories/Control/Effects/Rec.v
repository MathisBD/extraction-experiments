From Metaprog Require Import Prelude PluginLoader Control.Meta.

(** Due to technical details related to the positivity condition, recursive calls
    are represented using a [key], which is implemented as a natural.
    We keep track of the domain [A] and co-domain [B] of the function in the
    type of the key.

    At runtime a [key] is simply extracted to [int]. *)
Variant key (A : Type) (B : A -> Type) :=
| Key (k : nat).

(** The effect [recE] allows meta-programs to build fixpoints of functions
    without proving termination, and even to build non-terminating functions. *)
Variant recE (E : Type -> Type) : Type -> Type :=
| MkFix {A B} (F : key A B -> forall a : A, meta E (B a)) (a : A) : recE E (B a)
| Call {A B} (k : key A B) (a : A) : recE E (B a).

Arguments MkFix {E A B}.
Arguments Call {E A B}.

Section RecOperations.
  Context {E} `{recE E -< E}.

  (** Low-level function to build a fixpoint.
      Consider using a higher-level combinator [fixXXX] instead. *)
  Definition mkfix {A B} (F : key A B -> forall a : A, meta E (B a)) (a : A) : meta E (B a) :=
    trigger (MkFix F a).

  (** Low-level function to call the fixpoint parameter inside the body of a fixpoint.
      Consider using a higher-level combinator [fixXXX] instead. *)
  Definition call {A B} (k : key A B) (a : A) : meta E (B a) :=
    trigger (Call k a).

  (** *** Dependent fixpoint combinators. *)

  (** Take the fixpoint of a dependent function of one argument. *)
  Definition fix1 {A : Type} {B : A -> Type}
    (F : (forall a, meta E (B a)) -> (forall a, meta E (B a))) : forall a, meta E (B a) :=
    @mkfix A B (fun k a => F (call k) a).

  Definition fix2 {A1 : Type} {A2 : A1 -> Type} {B : forall a1, A2 a1 -> Type}
    (F : (forall a1 a2, meta E (B a1 a2)) -> (forall a1 a2, meta E (B a1 a2))) : forall a1 a2, meta E (B a1 a2) :=
    fun a1 a2 =>
      @fix1 { a1 & A2 a1 } (fun '⟨a1, a2⟩ => B a1 a2)
        (fun f '⟨a1, a2⟩ => F (fun a1 a2 => f ⟨a1, a2⟩) a1 a2)
        ⟨a1, a2⟩.

  Definition fix3 {A1 : Type} {A2 : A1 -> Type} {A3 : forall a1, A2 a1 -> Type} {B : forall a1 a2, A3 a1 a2 -> Type}
    (F : (forall a1 a2 a3, meta E (B a1 a2 a3)) -> (forall a1 a2 a3, meta E (B a1 a2 a3))) :
    forall a1 a2 a3, meta E (B a1 a2 a3) :=
    fun a1 a2 a3 =>
      @fix1 { a1 & { a2 & A3 a1 a2 } } (fun '⟨a1, ⟨a2, a3⟩⟩ => B a1 a2 a3)
        (fun f '⟨a1, ⟨a2, a3⟩⟩ => F (fun a1 a2 a3 => f ⟨a1, ⟨a2, a3⟩⟩) a1 a2 a3)
        ⟨a1, ⟨a2, a3⟩⟩.

  Definition fix4 {A1 : Type} {A2 : A1 -> Type} {A3 : forall a1, A2 a1 -> Type}
    {A4 : forall a1 a2, A3 a1 a2 -> Type} {B : forall a1 a2 a3, A4 a1 a2 a3 -> Type}
    (F : (forall a1 a2 a3 a4, meta E (B a1 a2 a3 a4)) -> (forall a1 a2 a3 a4, meta E (B a1 a2 a3 a4))) :
    forall a1 a2 a3 a4, meta E (B a1 a2 a3 a4) :=
    fun a1 a2 a3 a4 =>
      @fix1 { a1 & { a2 & { a3 & A4 a1 a2 a3 } } } (fun '⟨a1, ⟨a2, ⟨a3, a4⟩⟩⟩ => B a1 a2 a3 a4)
        (fun f '⟨a1, ⟨a2, ⟨a3, a4⟩⟩⟩ => F (fun a1 a2 a3 a4 => f ⟨a1, ⟨a2, ⟨a3, a4⟩⟩⟩) a1 a2 a3 a4)
        ⟨a1, ⟨a2, ⟨a3, a4⟩⟩⟩.

  Definition fix5 {A1 : Type} {A2 : A1 -> Type} {A3 : forall a1, A2 a1 -> Type}
    {A4 : forall a1 a2, A3 a1 a2 -> Type} {A5 : forall a1 a2 a3, A4 a1 a2 a3 -> Type}
    {B : forall a1 a2 a3 a4, A5 a1 a2 a3 a4 -> Type}
    (F : (forall a1 a2 a3 a4 a5, meta E (B a1 a2 a3 a4 a5)) -> (forall a1 a2 a3 a4 a5, meta E (B a1 a2 a3 a4 a5))) :
    forall a1 a2 a3 a4 a5, meta E (B a1 a2 a3 a4 a5) :=
    fun a1 a2 a3 a4 a5 =>
      @fix1 { a1 & { a2 & { a3 & { a4 & A5 a1 a2 a3 a4 } } } } (fun '⟨a1, ⟨a2, ⟨a3, ⟨a4, a5⟩⟩⟩⟩ => B a1 a2 a3 a4 a5)
        (fun f '⟨a1, ⟨a2, ⟨a3, ⟨a4, a5⟩⟩⟩⟩ => F (fun a1 a2 a3 a4 a5 => f ⟨a1, ⟨a2, ⟨a3, ⟨a4, a5⟩⟩⟩⟩) a1 a2 a3 a4 a5)
        ⟨a1, ⟨a2, ⟨a3, ⟨a4, a5⟩⟩⟩⟩.

End RecOperations.

(** Support for the [MetaFixpoint] command. *)

Register fix1 as metaprog.control.effects.rec.fix1.
Register fix2 as metaprog.control.effects.rec.fix2.
Register fix3 as metaprog.control.effects.rec.fix3.
Register fix4 as metaprog.control.effects.rec.fix4.
Register fix5 as metaprog.control.effects.rec.fix5.


(** 1-argument letrec notation. *)

(*Notation "'letrec%' f a ':=' body 'in' cont" :=
  (let f := fix1 (fun f a => body) in cont)
  (at level 200, no associativity, f ident, a pattern, only parsing).

Notation "'letrec%' f a ':' T ':=' body 'in' cont" :=
  (let f := (fix1 (fun f a => body) : (forall a, T)) in cont)
  (at level 200, no associativity, f ident, a pattern, only parsing).

(** 2-argument letrec notation. *)

Notation "'letrec%' f a1 a2 ':=' body 'in' cont" :=
  (let f := fix2 (fun f a1 a2 => body) in cont)
  (at level 200, no associativity, f ident, a1 pattern, a2 pattern, only parsing).

Notation "'letrec%' f a1 a2 ':' T ':=' body 'in' cont" :=
  (let f := (fix2 (fun f a1 a2 => body) : (forall a1 a2, T)) in cont)
  (at level 200, no associativity, f ident, a1 pattern, a2 pattern, only parsing).

(** 3-argument letrec notation. *)

Notation "'letrec%' f a1 a2 a3 ':=' body 'in' cont" :=
  (let f := fix3 (fun f a1 a2 a3 => body) in cont)
  (at level 200, no associativity, f ident, a1 pattern, a2 pattern, a3 pattern, only parsing).

Notation "'letrec%' f a1 a2 a3 ':' T ':=' body 'in' cont" :=
  (let f := (fix3 (fun f a1 a2 a3 => body) : (forall a1 a2 a3, T)) in cont)
  (at level 200, no associativity, f ident, a1 pattern, a2 pattern, a3 pattern, only parsing).

(** 4-argument letrec notation. *)

Notation "'letrec%' f a1 a2 a3 a4 ':=' body 'in' cont" :=
  (let f := fix4 (fun f a1 a2 a3 a4 => body) in cont)
  (at level 200, no associativity, f ident, a1 pattern, a2 pattern, a3 pattern, a4 pattern, only parsing).

Notation "'letrec%' f a1 a2 a3 a4 ':' T ':=' body 'in' cont" :=
  (let f := (fix4 (fun f a1 a2 a3 a4 => body) : (forall a1 a2 a3 a4, T)) in cont)
  (at level 200, no associativity, f ident, a1 pattern, a2 pattern, a3 pattern, a4 pattern, only parsing).

(** 5-argument letrec notation. *)

Notation "'letrec%' f a1 a2 a3 a4 a5 ':=' body 'in' cont" :=
  (let f := fix5 (fun f a1 a2 a3 a4 a5 => body) in cont)
  (at level 200, no associativity, f ident, a1 pattern, a2 pattern, a3 pattern, a4 pattern, a5 pattern, only parsing).

Notation "'letrec%' f a1 a2 a3 a4 a5 ':' T ':=' body 'in' cont" :=
  (let f := (fix5 (fun f a1 a2 a3 a4 a5 => body) : (forall a1 a2 a3 a4 a5, T)) in cont)
  (at level 200, no associativity, f ident, a1 pattern, a2 pattern, a3 pattern, a4 pattern, a5 pattern, only parsing).*)
