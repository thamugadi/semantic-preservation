Require Import Vector.
Import Vector.VectorNotations.

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

Fixpoint to_nat {n} (x : Fin.t n) : nat :=
  match x with
  | Fin.F1 => 0
  | Fin.FS t => 1 + (to_nat t)
  end.

Definition make_f1 (n : nat) (H : n <> 0) : Fin.t n.
Proof.
  destruct n eqn:H1.
  - unfold not in H. assert (0 = 0). reflexivity. contradiction.
  - exact Fin.F1.
Defined.

Definition make_fn (n : nat) (x : nat) (H : n <> 0) : Fin.t n :=
  match Fin.of_nat x n with
  | inleft p => p
  | inright _ => make_f1 n H
  end.

Definition strengthen {n} (x : Fin.t (S n)) (H : Common.to_nat x <> n) : Fin.t n.
Proof.
  destruct n.
  assert (x = Fin.F1).
  dependent destruction x.
  contradiction.
  inversion x.
  rewrite H0 in H.
  contradiction.
  apply Common.make_fn.
  exact (Common.to_nat x).
  lia.
Defined.

Definition minus {n} (x : Fin.t (S n)) (H : n <> 0) : Fin.t n.
Proof.
  destruct n eqn:H0.
  - contradiction.
  - destruct x eqn:H1.
    + exact Fin.F1.
    + apply Common.make_fn.
      exact (Common.to_nat t).
      unfold not. contradiction.
Defined.

End Common.
