Require Import List.
Import ListNotations.

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

Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0, _ => []
  | _, [] => []
  | S n', h::t => h :: take n' t
  end.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match n, l with
  | 0, _ => l
  | _, [] => []
  | S n', h::t => drop n' t
  end.

Fixpoint init {A} (l : list A) : list A :=
  match l with
  | [] => []
  | cons _ [] => []
  | cons x xs => cons x (init xs)
  end.

End Common.
