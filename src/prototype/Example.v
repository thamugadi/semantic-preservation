Require Import List.
Require Import Nat.
Require Import Lia.
Require Import Program.Equality.
Require Import Classical.
Import ListNotations.
From Hammer Require Import Tactics.
From Hammer Require Import Hammer.

Inductive instr1 : Type := | Load : instr1 | Halt : instr1.
Inductive instr2 : Type := | Load' : instr2 | Halt' : instr2.
Definition compile (p : list instr1) : list instr2 :=
  flat_map (fun i => match i with
                      | Load => [Load'; Load']
                      | Halt => [Halt']
                      end) p.

Fixpoint compile_index' (p : list instr1) (x a b : nat) : option nat :=
  match p, a =? x with
  | [], _ => None
  | _, true => Some b
  | i :: t, _ => compile_index' t x (a+1) (b+(length (compile [i])))
  end.

Definition compile_index (p : list instr1) (x : nat) : option nat :=
  compile_index' p x 0 0.

Compute (compile_index [Load;Load;Load] 2).

Fixpoint index {a} (p : list a) (x : nat) : option a :=
  match p with
  | [] => None
  | i :: t => if x =? 0 then Some i else index t (pred x)
  end.

Definition comp_instr (i : instr1) : instr2 := match i with | Halt => Halt' | Load => Load' end.

Theorem thg : forall p x x' i a b, compile_index' p x a b = Some x' -> index p x = Some i -> index (compile p) x' = Some (comp_instr i).
Proof.
Admitted.