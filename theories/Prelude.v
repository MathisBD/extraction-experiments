From Stdlib Require Export Bool Nat List Lia PrimString Relations Morphisms.
From Equations Require Export Equations.
From Metaprog Require Export Axioms.

Export PrimString.PStringNotations.
Export List.ListNotations.

(** Right-associative function application. *)
Notation "f '$' x" := (f x)
  (at level 67, right associativity, only parsing).

Ltac split3 := split ; [|split].
Ltac split4 := split ; [|split3].
Ltac split5 := split ; [|split4].
Ltac split6 := split ; [|split5].
Ltac split7 := split ; [|split6].
Ltac split8 := split ; [|split7].

(** On a hypothesis of the form [H : A -> B], [feed H] generates two goals:
    - the first asks to prove [A].
    - the second asks to prove the original goal in a context where [H : A]. *)
Ltac feed H :=
  match type of H with
  | ?A -> ?B =>
    let HA := fresh "H" in
    assert (HA : A) ; [| specialize (H HA) ; clear HA]
  end.

Ltac feed2 H := feed H ; [| feed H].
Ltac feed3 H := feed H ; [| feed2 H].
Ltac feed4 H := feed H ; [| feed3 H].

(** Compute the sum of a list of naturals.
    Returns [0] if the list is empty. *)
Equations sum : list nat -> nat :=
sum [] := 0 ;
sum (x :: xs) := x + sum xs.

Equations option_apply {A B} : option (A -> B) -> option A -> option B :=
option_apply (Some f) (Some x) := Some (f x) ;
option_apply _ _ := None.

Equations option_sequence {A} : list (option A) -> option (list A) :=
option_sequence [] := Some nil ;
option_sequence (None :: _) := None ;
option_sequence (Some x :: xs) := option_map (cons x) (option_sequence xs).

(** Ternary version of [sigT]. *)
Inductive sigT3 (A : Type) (P Q R : A -> Type) : Type :=
  existT3 : forall x : A, P x -> Q x -> R x -> sigT3 A P Q R.
Arguments sigT3 [A].
Arguments existT3 [A].

Notation "{ x & P & Q & R }" := (sigT3 (fun x => P) (fun x => Q) (fun x => R))
  (at level 0, x at level 99) : type_scope.

(** Notations to construct sigma-types. *)
Notation "⟨ x , y ⟩" := (existT _ x y).
Notation "⟨ x , y1 , y2 ⟩" := (existT2 _ _ x y1 y2).
Notation "⟨ x , y1 , y2 , y3 ⟩" := (existT3 _ _ _ x y1 y2 y3).

Derive Signature for Forall Exists.

(** [OnOne2 P xs ys] means that the lists [xs] and [ys] are equal except at
    exactly one position, and at these positions the elements are related by [P]. *)
Inductive OnOne2 {A} (P : A -> A -> Prop) : list A -> list A -> Prop :=
| OnOne2_head x x' xs : P x x' -> OnOne2 P (x :: xs) (x' :: xs)
| OnOne2_tail x xs xs' : OnOne2 P xs xs' -> OnOne2 P (x :: xs) (x :: xs').

Derive Signature for OnOne2.

Lemma OnOne2_length {A} (P : A -> A -> Prop) xs ys :
  OnOne2 P xs ys -> List.length xs = List.length ys.
Proof. intros H. induction H ; cbn ; lia. Qed.

Lemma OnOne2_app_l {A} (P : A -> A -> Prop) xs xs' ys :
  OnOne2 P xs xs' -> OnOne2 P (xs ++ ys) (xs' ++ ys).
Proof.
intros H. induction H ; cbn.
- now apply OnOne2_head.
- now apply OnOne2_tail.
Qed.

Lemma OnOne2_app_r {A} (P : A -> A -> Prop) xs ys ys' :
  OnOne2 P ys ys' -> OnOne2 P (xs ++ ys) (xs ++ ys').
Proof.
intros H. induction xs ; cbn.
- assumption.
- now apply OnOne2_tail.
Qed.

Lemma OnOne2_consequence {A} (P Q : A -> A -> Prop) xs ys :
  (forall x y, P x y -> Q x y) ->
  OnOne2 P xs ys ->
  OnOne2 Q xs ys.
Proof.
intros H H'. induction H'.
- apply OnOne2_head. auto.
- now apply OnOne2_tail.
Qed.

Lemma OnOne2_map {A A'} (P : A' -> A' -> Prop) (f : A -> A') xs ys :
  OnOne2 (fun x y => P (f x) (f y)) xs ys ->
  OnOne2 P (map f xs) (map f ys).
Proof.
intros H. depind H ; cbn.
- now constructor.
- now constructor.
Qed.

(** [All2 P xs ys] means that [P] holds on every element of [xs] and [ys].
    In particular [xs] and [ys] must have the same length. *)
Inductive All2 {A B} (P : A -> B -> Prop) : list A -> list B -> Prop :=
| All2_nil : All2 P [] []
| All2_cons x xs y ys : P x y -> All2 P xs ys -> All2 P (x :: xs) (y :: ys).

Derive Signature for All2.

Lemma All2_length {A B} (P : A -> B -> Prop) xs ys :
  All2 P xs ys -> List.length xs = List.length ys.
Proof. intros H ; induction H ; cbn ; lia. Qed.

Lemma All2_app {A B} (P : A -> B -> Prop) xs xs' ys ys' :
  All2 P xs xs' -> All2 P ys ys' -> All2 P (xs ++ ys) (xs' ++ ys').
Proof.
intros H1 H2. induction H1 ; cbn.
- assumption.
- now constructor.
Qed.

Lemma All2_consequence {A} (P Q : A -> A -> Prop) xs ys :
  (forall x y, P x y -> Q x y) ->
  All2 P xs ys ->
  All2 Q xs ys.
Proof. intros H H'. induction H' ; constructor ; auto. Qed.

#[export] Instance All2_Reflexive {A} (P : A -> A -> Prop) :
  Reflexive P -> Reflexive (All2 P).
Proof. intros H xs. induction xs ; now constructor. Qed.

Lemma All2_of_OnOne2 {A} (P : A -> A -> Prop) xs ys :
  Reflexive P -> OnOne2 P xs ys -> All2 P xs ys.
Proof. intros HR H. induction H ; now constructor. Qed.

Lemma All2_map {A A' B B'} (P : A' -> B' -> Prop) (f : A -> A') (g : B -> B') xs ys :
  All2 P (map f xs) (map g ys) <->
  All2 (fun x y => P (f x) (g y)) xs ys.
Proof.
split ; intros H ; depind H.
- destruct xs ; [| depelim H]. destruct ys ; [| depelim H0].
  constructor.
- destruct xs0 ; [depelim H1 |]. destruct ys0 ; [depelim H2 |].
  cbn in H1, H2. depelim H1. depelim H2. constructor.
  + assumption.
  + apply IHAll2. reflexivity.
- constructor.
- now constructor.
Qed.
