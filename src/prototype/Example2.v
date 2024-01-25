Require Import Vector.
Import Vector.VectorNotations.
Require Import Program.Equality.
Require Import Coq.Program.Wf.
From Hammer Require Import Tactics.
From Hammer Require Import Hammer.
Require Import Lia.

Inductive instr1 : Type :=
  | A : instr1
  | B : instr1.

Inductive instr2 : Type :=
  | A' : instr2
  | B' : instr2
  | C' : instr2.

Fixpoint comp_len {n} (p : t instr1 n) : nat :=
  match p with
  | [] => 0
  | A :: xs => 1 + comp_len xs
  | B :: xs => 3 + comp_len xs
  end.

Fixpoint compile {n} (p : Vector.t instr1 n) : Vector.t instr2 (comp_len p).
Proof.
  destruct p.
  exact [].
  destruct h.
  - exact (A' :: compile n p).
  - exact (C' :: B' :: A' :: compile n p).
Defined.

Fixpoint compile_index {n} (p : t instr1 n) (x : Fin.t n) : Fin.t (comp_len p).
Proof.
  destruct x eqn:H1; rewrite (eta p); destruct hd eqn:H2.
  - apply Fin.F1.
  - apply Fin.F1.
  - do 1 apply Fin.FS. apply compile_index. exact t.
  - do 3 apply Fin.FS. apply compile_index. exact t.
Defined.

Fixpoint to_nat {n} (x : Fin.t n) : nat.
Proof.
  destruct x eqn:H.
  - exact 0.
  - apply plus.
    + exact 1.
    + apply to_nat with (n := n).
      exact t.
Defined.

Definition vec_len {A n} (v : Vector.t A n) : nat := n.

Theorem th2 {n} : forall p q x x' i (off : Fin.t (vec_len (compile [i]))),
                  q = compile p -> p[@x] = i ->
                  to_nat x' = to_nat (@compile_index n p x) + to_nat off ->
                  q[@x'] = (compile [i])[@off].
Admitted.