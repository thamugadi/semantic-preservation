Require Import Vector.
Import Vector.VectorNotations.
Require Import Program.Equality.

Inductive instr1 : Type :=
  | Load : instr1
  | Halt : instr1.

Inductive instr2 {n} : Type :=
  | Load' : instr2
  | Halt' : Fin.t n -> instr2.

Definition make_f1 (x : nat) (H : x <> 0) : Fin.t x.
Proof.
  destruct x eqn:H1.
  - auto with *.
  - exact Fin.F1.
Defined.

Definition comp_instr {n : nat} (HA : n <> 0) x :=
  match x with
  | Load => Load'
  | Halt => Halt' (make_f1 n HA)
  end.

Fixpoint comp_len {n} (p : t instr1 n) : nat :=
  match p with
  | Vector.nil _ => 0
  | Halt :: xs => 1 + comp_len xs
  | Load :: xs => 2 + comp_len xs
  end.

Fixpoint compile' {n n'} (HA : n' <> 0) (p : t instr1 n) : t (@instr2 n') (comp_len p).
Proof.
  destruct p.
  - exact [].
  - destruct h.
    + cbn.
      exact ((Load' :: Load' :: (compile' n n' HA p))).
    + cbn.
      exact ((Halt' (make_f1 n' HA)) :: (compile' n n' HA p)).
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

Fixpoint weaken_fin_t {n : nat} (f : Fin.t n) : Fin.t (S n) :=
  match f in Fin.t n return Fin.t (S n) with
  | Fin.F1 => Fin.F1
  | Fin.FS f' => Fin.FS (weaken_fin_t f')
  end.
Require Import Coq.Program.Wf.
From Hammer Require Import Tactics.
Require Import Lia.
Program Fixpoint fin_t_fact {n} (i : Fin.t n) {measure (to_nat i)} : nat :=
  match i with
  | Fin.F1 => 1
  | Fin.FS t => (to_nat i) * (fin_t_fact (weaken_fin_t t))
  end.
Next Obligation.
  dependent destruction t.
  - ssimpl.
  - ssimpl.
    assert (to_nat (weaken_fin_t t) = to_nat t).
    + dependent induction t. ssimpl.
      ssimpl.
    + rewrite H. lia.
Qed.
Check (nat, bool).

Fixpoint make_indexes (n : nat) : Vector.t (Fin.t n) n :=
  match n with
  | 0 => []
  | S i => Fin.F1 :: map Fin.FS (make_indexes i)
  end.

Compute (make_indexes 8).

Lemma lm1 : forall n p, n <> 0 -> @comp_len n p <> 0.
Proof.
  intros. destruct p. auto with *. destruct h; cbn; auto with *.
Qed.
Definition compile {n : nat} (p : t instr1 n) (HA : n <> 0) : t (@instr2 (comp_len p)) (comp_len p) :=
  @compile' n (comp_len p) (lm1 n p HA) p.

Fixpoint compile_index {n} (p : t instr1 n) (x : Fin.t n) : Fin.t (comp_len p).
Proof.
  destruct x eqn:H1; rewrite (eta p); destruct hd eqn:H2.
  - apply Fin.F1.
  - apply Fin.F1.
  - do 2 apply Fin.FS. apply compile_index. exact t.
  - do 1 apply Fin.FS, compile_index. exact t.
Defined.

Theorem th : forall {n} (x : Fin.t n) (p : Vector.t instr1 n) (HA : n <> 0),
  @comp_instr (comp_len p) (lm1 n p HA) p[@x] = (@compile n p HA)[@compile_index p x].
Admitted.



