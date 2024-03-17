Require Import List.
Require Import Nat.
Require Import Lia.
Import ListNotations.

From Hammer Require Import Tactics.

Inductive lookup {A : Type} : list A -> nat -> A -> Prop :=
  | lu1 : forall x xs, lookup (x :: xs) 0 x
  | lu2 : forall x xs i y, lookup xs i y -> lookup (x :: xs) (S i) y.
Inductive instr1 : Type := | Load : instr1 | Halt : instr1.
Inductive instr2 : Type := | Load' : instr2 | Halt' : instr2.
Fixpoint compile (p : list instr1) : list instr2 :=
  match p with
  | [] => []
  | Load :: h => Load'::Load'::compile h
  | Halt :: h => Halt'::compile h
  end.
Definition comp_first (i : instr1) : instr2 := 
  match i with | Halt => Halt' | Load => Load' end.
Fixpoint compile_index (p : list instr1) (x : nat) : nat :=
  match x with
  | 0 => 0
  | _ => match p with
         | [] => 0
         | Load :: h => 2 + compile_index h (x-1)
         | Halt :: h => 1 + compile_index h (x-1)
         end
  end.

Lemma lm6 : forall a p, compile (a :: p) = [] -> False.
Proof.
  intros.
  induction p;
  destruct a; simpl;
  discriminate.
Qed.

Lemma trv : forall n, n - 0 = n.
Proof. lia. Qed.

Theorem th :
  forall p q i x, compile p = q -> lookup p x i ->
  lookup q (compile_index p x) (comp_first i).
Proof.
  induction p; destruct q; destruct i; intros; try inversion H.
  - inversion H0.
  - inversion H0.
  - exfalso.
    apply lm6 with (a := a) (p := p).
    assumption.
  - exfalso.
    apply lm6 with (a := a) (p := p).
    assumption.
  - ssimpl; apply lu2.
    rewrite trv.
    inversion H. apply lu2. apply lu1.
    apply lu2. apply lu2. assumption.
  - ssimpl; apply lu2.
    rewrite trv.
    apply IHp.
    reflexivity.
    assumption.
Qed.

Theorem comp_instr : forall prog pc i, lookup prog pc i ->
                     lookup (compile prog) (compile_index prog pc) (comp_first i).
Proof.
  intros.
  assert (forall p q i x, compile p = q -> lookup p x i ->
          lookup q (compile_index p x) (comp_first i)).
  apply th.
  apply H0.
  reflexivity.
  assumption.
Qed.