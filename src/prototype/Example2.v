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

Lemma to_nat_z {n} : forall a, to_nat a = 0 -> a = @Fin.F1 n.
Proof.
  intros.
  dependent destruction a.
  reflexivity.
  exfalso.
  inversion H.
Qed.

Theorem th {n} : forall p x x' i (off : Fin.t (comp_len [i])),
                  p[@x] = i ->
                  to_nat x' = to_nat (@compile_index n p x) + to_nat off ->
                  (compile p)[@x'] = (compile [i])[@off].
Proof.
  intros.
  destruct i; dependent destruction off.
  - simpl in *.
    assert (x' = compile_index p x). apply to_nat_st. lia.
    rewrite H1.
    assert (A' = compile_first p[@x]). rewrite H. now reflexivity.
    rewrite H2.
    apply read_instr_eq.
  - inversion off.
  - simpl in *.
    assert (x' = compile_index p x). apply to_nat_st. lia.
    rewrite H1.
    assert (C' = compile_first p[@x]). rewrite H. now reflexivity.
    rewrite H2.
    apply read_instr_eq.
  - dependent destruction off.
    + simpl in *.
      admit.
    + dependent destruction off.
      * simpl in *.
        admit.
      * inversion off.
Admitted.