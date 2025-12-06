From Metaprog Require Import Prelude MetaMonad.

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
  Definition fix1_dep {A : Type} {B : A -> Type}
    (F : (forall a, meta E (B a)) -> (forall a, meta E (B a))) : forall a, meta E (B a) :=
    @mkfix A B (fun k a => F (call k) a).

  Definition fix2_dep {A1 : Type} {A2 : A1 -> Type} {B : forall a1, A2 a1 -> Type}
    (F : (forall a1 a2, meta E (B a1 a2)) -> (forall a1 a2, meta E (B a1 a2))) : forall a1 a2, meta E (B a1 a2) :=
    fun a1 a2 =>
      @fix1_dep { a1 & A2 a1 } (fun '⟨a1, a2⟩ => B a1 a2)
        (fun f '⟨a1, a2⟩ => F (fun a1 a2 => f ⟨a1, a2⟩) a1 a2)
        ⟨a1, a2⟩.

  Definition fix3_dep {A1 : Type} {A2 : A1 -> Type} {A3 : forall a1, A2 a1 -> Type} {B : forall a1 a2, A3 a1 a2 -> Type}
    (F : (forall a1 a2 a3, meta E (B a1 a2 a3)) -> (forall a1 a2 a3, meta E (B a1 a2 a3))) : forall a1 a2 a3, meta E (B a1 a2 a3) :=
    fun a1 a2 a3 =>
      @fix1_dep { a1 & { a2 & A3 a1 a2 } } (fun '⟨a1, ⟨a2, a3⟩⟩ => B a1 a2 a3)
        (fun f '⟨a1, ⟨a2, a3⟩⟩ => F (fun a1 a2 a3 => f ⟨a1, ⟨a2, a3⟩⟩) a1 a2 a3)
        ⟨a1, ⟨a2, a3⟩⟩.

  (** *** Non-dependent fixpoint combinators. *)

  (** Take the fixpoint of a non-dependent function of one argument. *)
  Definition fix1 {A B : Type} (F : (A -> meta E B) -> (A -> meta E B)) : A -> meta E B :=
    @mkfix A (fun _ => B) (fun k a => F (call k) a).

  (** Take the fixpoint of a non-dependent function of two arguments. *)
  Definition fix2 {A1 A2 B : Type}
    (F : (A1 -> A2 -> meta E B) -> (A1 -> A2 -> meta E B)) : A1 -> A2 -> meta E B :=
    fun a1 a2 =>
      @mkfix (A1 * A2) (fun _ => B)
        (fun k '(a1, a2) => F (fun a1 a2 => call k (a1, a2)) a1 a2)
        (a1, a2).

  (** Take the fixpoint of a non-dependent function of three arguments. *)
  Definition fix3 {A1 A2 A3 B : Type}
    (F : (A1 -> A2 -> A3 -> meta E B) -> (A1 -> A2 -> A3 -> meta E B)) : A1 -> A2 -> A3 -> meta E B :=
    fun a1 a2 a3 =>
      @mkfix (A1 * A2 * A3) (fun _ => B)
        (fun k '(a1, a2, a3) => F (fun a1 a2 a3 => call k (a1, a2, a3)) a1 a2 a3)
        (a1, a2, a3).

End RecOperations.


Notation "'letrec' f a ':=' body 'in' cont" :=
  (let f := fix1_dep (fun f a => body) in cont)
  (at level 200, no associativity, f binder, a pattern, only parsing).

Notation "'letrec' f a ':' T ':=' body 'in' cont" :=
  (let f := (fix1_dep (fun f a => body) : (forall a, T)) in cont)
  (at level 200, no associativity, f binder, a pattern, only parsing).

Notation "'letrec' f a1 a2 ':=' body 'in' cont" :=
  (let f := fix2_dep (fun f a1 a2 => body) in cont)
  (at level 200, no associativity, f binder, a1 pattern, a2 pattern, only parsing).

Notation "'letrec' f a1 a2 ':' T ':=' body 'in' cont" :=
  (let f := (fix2_dep (fun f a1 a2 => body) : (forall a1 a2, T)) in cont)
  (at level 200, no associativity, f binder, a1 pattern, a2 pattern, only parsing).


Notation "'letrec' f a1 a2 a3 ':=' body 'in' cont" :=
  (let f := fix3_dep (fun f a1 a2 a3 => body) in cont)
  (at level 200, no associativity, f binder, a1 pattern, a2 pattern, a3 pattern, only parsing).

Notation "'letrec' f a1 a2 a3 ':' T ':=' body 'in' cont" :=
  (let f := (fix3_dep (fun f a1 a2 a3 => body) : (forall a1 a2 a3, T)) in cont)
  (at level 200, no associativity, f binder, a1 pattern, a2 pattern, a3 pattern, only parsing).
