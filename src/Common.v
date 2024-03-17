Require Import List.
Import List.ListNotations.

Require Import Coq.Program.Equality.
Require Import Lia.

Module Common.

Definition embed {A : Type} {B : Type} (f : A -> B) :=
   fun x y => y = f x.

Inductive star {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  | rt_refl : forall x, star R x x
  | rt_trans : forall x y z, R x y -> star R y z -> star R x z.

Theorem rt_step {A} (R : A -> A -> Prop) :
  forall x y, R x y -> (star R) x y.
Proof.
  intros x y H.
  apply rt_trans with (x := x) (y := y) (z := y).
  assumption.
  apply rt_refl.
Qed.

Inductive plus {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  | t_base : forall x y, R x y -> plus R x y
  | t_trans : forall x y z, R x y -> plus R y z -> plus R x z.

Inductive lookup {A : Type} : list A -> nat -> A -> Prop :=
  | lu1 : forall x xs, lookup (x :: xs) 0 x
  | lu2 : forall x xs i y, lookup xs i y -> lookup (x :: xs) (S i) y.

Inductive list_eq_except {A} (m1 m2 : list A) (indexes : list nat) : Prop :=
  | md : (forall i e, ~ (In i indexes) -> lookup m1 i e -> lookup m2 i e) ->
         list_eq_except m1 m2 indexes.


End Common.
