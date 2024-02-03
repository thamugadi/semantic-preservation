Require Import Vector.
Import Vector.VectorNotations.

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

Fixpoint to_nat {n} (x : Fin.t n) : nat.
Proof.
  destruct x eqn:H.
  - exact 0.
  - apply plus.
    + exact 1.
    + apply to_nat with (n := n).
      exact t.
Defined.

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

Inductive plus {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  | t_base : forall x y, R x y -> plus R x y
  | t_trans : forall x y z, R x y -> plus R y z -> plus R x z.

End Common.
