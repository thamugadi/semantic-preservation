Require Import Vector.
Import Vector.VectorNotations.
Require Import Program.Equality.
Require Import Coq.Program.Wf.
From Hammer Require Import Tactics.
From Hammer Require Import Hammer.
Require Import Lia.
Require Import Classical.

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

Fixpoint to_nat {n} (x : Fin.t n) : nat :=
  match x with
  | Fin.F1 => 0
  | Fin.FS t => 1 + (to_nat t)
  end.


Definition vec_len {A n} (v : Vector.t A n) : nat := n.

Definition compile_first (i : instr1) : instr2 :=
  match i with
  | A => A'
  | B => C'
  end.

Lemma read_instr_eq {n} : forall p x,
                          (compile p)[@@compile_index n p x] = @compile_first p[@x].
Proof.
  intros.
  induction x; dependent destruction p;
  destruct h; simpl;
  try (now reflexivity);
  try (apply IHx).
Qed.

Lemma to_nat_st {n} : forall a b, @to_nat n a = to_nat b -> a = b.
Proof.
  intros.
  dependent induction a; dependent destruction b.
  reflexivity.
  assert (n = 0). ssimpl. exfalso. ssimpl.
  assert (n = 0). ssimpl. exfalso. ssimpl.
  f_equal.
  apply IHa.
  inversion H.
  reflexivity.
Qed.
Require Import Coq.Arith.Arith_base.

Definition fint_plus {n m} (a : Fin.t n) (b : Fin.t m) : Fin.t (n + m).
Proof.
  induction a.
  * induction b.
    ** exact Fin.F1.
    ** rewrite Nat.add_comm. cbn. apply Fin.FS. rewrite Nat.add_comm. assumption.
  * cbn. apply Fin.FS. assumption.
Defined.

Lemma ci_le {n} : forall p x, to_nat (@compile_index n p x) <
                              comp_len p - vec_len (compile [p[@x]]) + 1.
Admitted.

Definition safe_plus {n m} (a : Fin.t n) (b : Fin.t m)
                           (H : (to_nat a) + (to_nat b) < n) : Fin.t n.
Admitted.

Lemma safe_plus_is_plus {n m} : forall a b H,
                                @to_nat n (safe_plus a b H) =
                                (to_nat a) + (@to_nat m b).
Admitted. 

Require Import Coq.Vectors.VectorDef.

Fixpoint drop_fill {n a} (p : t a n) (f : a) (i : nat) : t a n.
Admitted.

Theorem th {n} :  forall p x x' (off : Fin.t (comp_len [p[@x]])),
                  to_nat x' = to_nat (@compile_index n p x) + to_nat off ->
                  (compile p)[@x'] = (compile [p[@x]])[@off].
Proof.
  intros.
  