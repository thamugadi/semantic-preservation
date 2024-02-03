Require Import Vector.
Import Vector.VectorNotations.
Require Import Program.Equality.
Require Import Coq.Program.Wf.
From Hammer Require Import Tactics.
From Hammer Require Import Hammer.
Require Import Lia.
Inductive instr1 : Type := | A : instr1 | B : instr1.
Inductive instr2 : Type := | A' : instr2 | B' : instr2 | C' : instr2.
Fixpoint comp_len {n} (p : t instr1 n) : nat :=
  match p with
  | [] => 0
  | A :: xs => 1 + comp_len xs
  | B :: xs => 3 + comp_len xs
  end.
Fixpoint compile {n} (p : Vector.t instr1 n) : Vector.t instr2 (comp_len p) :=
  match p with
  | [] => []
  | A :: p' => A' :: compile p'
  | B :: p' => C' :: B' :: A' :: compile p'
  end.
Fixpoint compile_index {n} (p : t instr1 n) (x : Fin.t n) : Fin.t (comp_len p).
Proof.
  destruct x eqn:H1; rewrite (eta p); destruct hd eqn:H2.
  - apply Fin.F1.
  - apply Fin.F1.
  - do 1 apply Fin.FS. apply compile_index. exact t.
  - do 3 apply Fin.FS. apply compile_index. exact t.
Defined.
Fixpoint to_nat {n} (x : Fin.t n) : nat :=
  match x with
  | Fin.F1 => 0
  | Fin.FS t => 1 + (to_nat t)
  end.

Theorem th {n} : forall p x x' (off : Fin.t (comp_len [p[@x]])),
                  to_nat x' = to_nat (@compile_index n p x) + to_nat off ->
                  (compile p)[@x'] = (compile [p[@x]])[@off].


