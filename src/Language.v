Require Import List.
Import ListNotations.
Require Import Common.
Require Import PeanoNat.
Import Nat.
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

Fixpoint read_instr' (prog : program) (pc : nat) : instr :=
  match prog, pc with
  | [], _ => Halt
  | i :: _, 0 => i
  | _ :: t, S pc' => read_instr' t pc'
  end.

Inductive read_instr (p : state) (i : instr) : Prop  :=
  | ri : read_instr' p.(prog) p.(pc) = i -> read_instr p i.

Fixpoint read_mem' (m : list nat) (index : nat) : nat :=
  match m, index with
  | [], _ => 0
  | i :: _, 0 => i
  | _ :: t, S index' => read_mem' t index'
  end.

Inductive read_mem (p : state) (n : nat) : Prop  :=
  | mi : read_mem' p.(mem) p.(ptr) = n -> read_mem p n.

Inductive mem_diff_p (m : list nat) (m' : list nat) (ptr : nat) : Prop :=
  | c_diff_p : Common.take ptr m = Common.take ptr m' ->
               Common.drop (ptr+1) m = Common.drop (ptr+1) m' ->
               Common.drop (ptr) (Common.take (ptr+1) m') = (map (fun x => x + 1))
               (Common.drop (ptr) (Common.take (ptr+1) m)) 
               -> mem_diff_p m m' ptr.

Inductive mem_diff_m (m : list nat) (m' : list nat) (ptr : nat) : Prop :=
  | c_diff_m : Common.take ptr m = Common.take ptr m' ->
               Common.drop (ptr+1) m = Common.drop (ptr+1) m' ->
               Common.drop (ptr) (Common.take (ptr+1) m') = (map (fun x => x - 1))
               (Common.drop (ptr) (Common.take (ptr+1) m)) 
               -> mem_diff_m m m' ptr.

(*Some cases will not be accepted for compilation anyway, like unmatched jumps.*)
(* Small-step operational semantics for our source language.*)
Inductive semantics (p : state) (p' : state) : Prop :=
  | ptr_inc : read_instr p PtrInc -> p.(ptr) + 1 = p'.(ptr) ->
                   p.(pc) + 1 = p'.(pc) -> p.(prog) = p'.(prog) ->
                   p.(mem) = p'.(mem) -> semantics p p' 
  | ptr_dec : read_instr p PtrDec -> p.(ptr) - 1 = p'.(ptr) ->
                   p.(pc) + 1 = p'.(pc) -> p.(prog) = p'.(prog) ->
                   p.(mem) = p'.(mem) -> semantics p p'
  | inc : read_instr p Inc -> p.(ptr) = p'.(ptr) ->
               length p.(mem) > p.(ptr) ->
               p.(pc) + 1 = p'.(pc) -> p.(prog) = p'.(prog) ->
               mem_diff_p p.(mem) p'.(mem) p.(ptr) -> semantics p p' 
  | dec : read_instr p Dec -> p.(ptr) = p'.(ptr) ->
               length p.(mem) > p.(ptr) ->
               p.(pc) + 1 = p'.(pc) -> p.(prog) = p'.(prog) ->
               mem_diff_m p.(mem) p'.(mem) p.(ptr) -> semantics p p' 
  | jump_z : read_instr p Jump -> p.(ptr) = p'.(ptr) ->
                  p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
                  length p.(mem) > p.(ptr) -> read_mem p 0 ->
                  semantics p p'
  | jump_nz : read_instr p Jump -> p.(ptr) = p'.(ptr) ->
                   p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
                   length p.(mem) > p.(ptr) -> ~ (read_mem p 0) ->
                   p.(pc) + 1 = p'.(pc) -> semantics p p'
  | ret_z :  read_instr p Jump -> p.(ptr) = p'.(ptr) ->
                  p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
                  length p.(mem) > p.(ptr) -> read_mem p 0 ->
                  semantics p p'
  | ret_nz : read_instr p Jump -> p.(ptr) = p'.(ptr) ->
                  p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
                  length p.(mem) > p.(ptr) -> ~ (read_mem p 0) ->
                  p.(pc) + 1 = p'.(pc) -> semantics p p'.
End Language.