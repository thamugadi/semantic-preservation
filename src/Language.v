Require Import Program.Equality.
Require Import PeanoNat.
Require Import Common.
Require Import Lia.
Require Import List.
Import List.ListNotations.
Module Language.
Inductive instr : Type :=
  | PtrInc : instr
  | PtrDec : instr
  | Inc : instr
  | Dec : instr
  | Jump : instr
  | Ret : instr
  | Halt : instr.
Definition program := list instr.

Record state : Type := mkState
{ 
  prog : program;
  mem : list nat;
  pc : nat;
  ptr : nat;
}.


Definition option_inc (i : option nat) : option nat :=
  match i with
  | None => None
  | Some a => Some (a + 1)
  end.


Fixpoint matching_jump' (l : list instr) (idx : nat) (c : nat) 
                        (c' : option nat) : option nat :=
  match l with
  | [] => None
  | Jump :: h => if c =? idx then None else matching_jump' h idx (c+1) (Some c)
  | Ret :: h => if c =? idx then (option_inc c') else None
  | _ :: h => if c =? idx then None else matching_jump' h idx (c+1) c'
  end.

Fixpoint matching_ret' (l : list instr) (idx : nat) (c c' : nat) :
                           option nat :=
  match l with
  | [] => None
  | i :: h => if c' <=? idx then matching_ret' h idx c (c'+1) else
    match i with
    | Jump => matching_ret' h idx (c+1) (c'+1)
    | Ret => if c =? 0 then (Some (c' + 1)) else matching_ret' h idx
             (c-1) (c'+1)
    | _ => matching_ret' h idx c (c'+1)
    end
end.

Inductive matching_jump (p : program) (x x' : nat) : Prop :=
  | mj : matching_jump' p x 0 None = Some x' -> matching_jump p x x'.
Inductive matching_ret (p : program) (x x' : nat) : Prop :=
  | mr : matching_ret' p x 0 0 = Some x' -> matching_ret p x x'.

(* Small-step operational semantics for our source language.*)

Definition read_instr (p : state) (i : instr) :=
  Common.lookup (prog p) (pc p) i.

Inductive semantics (p p' : state) : Prop :=
  | ptr_inc : read_instr p PtrInc -> prog p = prog p' -> pc p + 1 = pc p' ->
              ptr p + 1 = ptr p' -> mem p = mem p' -> semantics p p'
  | ptr_dec : read_instr p PtrDec -> prog p = prog p' -> pc p + 1 = pc p' ->
              ptr p - 1 = ptr p' -> mem p = mem p' -> semantics p p'
  | inc     : read_instr p Inc -> prog p = prog p' -> pc p + 1 = pc p' ->
              ptr p = ptr p' ->
              Common.list_eq_except (mem p) (mem p') [ptr p] ->
              (forall M, (Common.lookup (mem p) (ptr p) M ->
                         Common.lookup (mem p') (ptr p') (M+1))) -> semantics p p'
  | dec     : read_instr p Dec -> prog p = prog p' -> pc p + 1 = pc p' ->
              ptr p = ptr p' ->
              Common.list_eq_except (mem p) (mem p') [ptr p] ->
              (forall M, (Common.lookup (mem p) (ptr p) M ->
                         Common.lookup (mem p') (ptr p') (M-1))) -> semantics p p'
  | jump_z  : read_instr p Jump -> ptr p = ptr p' -> prog p = prog p' -> mem p = mem p' -> 
              Common.lookup (mem p) (ptr p) 0 -> matching_ret (prog p) (pc p) (pc p') ->
              semantics p p'
  | jump_nz : read_instr p Jump -> ptr p = ptr p' -> prog p = prog p' -> mem p = mem p' -> 
              ~(Common.lookup (mem p) (ptr p) 0) -> pc p + 1 = pc p' ->
              semantics p p'
  | ret_z   : read_instr p Ret -> ptr p = ptr p' -> prog p = prog p' -> mem p = mem p' -> 
              Common.lookup (mem p) (ptr p) 0 -> matching_jump (prog p) (pc p) (pc p') ->
              semantics p p'
  | ret_nz  : read_instr p Ret -> ptr p = ptr p' -> prog p = prog p' -> mem p = mem p' -> 
              ~(Common.lookup (mem p) (ptr p) 0) -> pc p + 1 = pc p' ->
              semantics p p'.
End Language.