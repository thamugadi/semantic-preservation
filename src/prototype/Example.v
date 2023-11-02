Require Import List.
Require Import Nat.
Require Import Lia.
Require Import Classical.
Import ListNotations.

Inductive instr1 : Type := | Load : instr1 | Halt : instr1.
Inductive instr2 : Type := | Load' : instr2 | Halt' : instr2.

Fixpoint compile (p : list instr1) : list instr2 :=
  match p with
  | [] => []
  | Load :: t => Load' :: Load' :: compile t
  | Halt :: t => Halt' :: compile t
  end.

Fixpoint compile_index' (p : list instr1) (x a b : nat) : option nat :=
  if (a =? x) then Some b else
  match p with
  | [] => None
  | Load :: t => compile_index' t x (a+1) (b+2)
  | Halt :: t => compile_index' t x (a+1) (b+1)
  end.

Definition compile_index (p : list instr1) (x : nat) : option nat := compile_index' p x 0 0.

Fixpoint index1 (p : list instr1) (x : nat) : option instr1 :=
  match p, x with
  | [], _ => None
  | i :: _, 0 => Some i
  | _ :: t, S x' => index1 t x'
  end.
Fixpoint index2 (p : list instr2) (x : nat) : option instr2 :=
  match p, x with
  | [], _ => None
  | i :: _, 0 => Some i
  | _ :: t, S x' => index2 t x'
  end.

Definition comp_instr (i : instr1) : instr2 :=
  match i with | Halt => Halt' | Load => Load' end.

Theorem th : forall p x x' i, compile_index p x = Some x' -> index1 p x = Some i ->
             index2 (compile p) x' = Some (comp_instr i).
Proof.
  