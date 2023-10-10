Require Import List.
Import ListNotations.
Require Import Common.
Require Import PeanoNat.
Import Nat.
Module Assembly.

Inductive asm_instr : Type :=
  | Load : nat -> asm_instr
  | Store : nat -> asm_instr
  | Add : nat -> asm_instr
  | Sub : nat -> asm_instr
  | Jump : nat -> asm_instr
  | Skip : asm_instr
  | Halt : asm_instr.

Definition asm_program := list asm_instr.

Record asm_state : Type := mkState
{ 
  prog : asm_program;
  mem : list nat;
  pc : nat;
  ac : nat;
}.

Fixpoint read_instr' (prog : asm_program) (pc : nat) : asm_instr :=
  match prog, pc with
  | [], _ => Halt
  | i :: _, 0 => i
  | _ :: t, S pc' => read_instr' t pc'
  end.

Inductive read_instr (p : asm_state) (i : asm_instr) : Prop  :=
  | ri : read_instr' p.(prog) p.(pc) = i -> read_instr p i.


Fixpoint read_mem' (m : list nat) (index : nat) : nat :=
  match m, index with
  | [], _ => 0
  | i :: _, 0 => i
  | _ :: t, S index' => read_mem' t index'
  end.

Inductive read_mem (p : asm_state) (n : nat) : Prop  :=
  | mi : read_mem' p.(mem) p.(ac) = n -> read_mem p n.

Inductive mem_diff (m : list nat) (m' : list nat) (ac : nat) (n : nat) : Prop :=
  | c_diff : Common.take ac m = Common.take ac m' ->
               Common.drop (ac+1) m = Common.drop (ac+1) m' ->
               Common.drop (ac) (Common.take (ac+1) m') = (map (fun x => n))
               (Common.drop (ac) (Common.take (ac+1) m)) 
               -> mem_diff m m' ac n.

Inductive lang_semantics (p : asm_state) (p' : asm_state) : Prop :=
  | asm_load : forall n, read_instr p (Load n) -> p.(pc) + 1 = p'.(pc) ->
               p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
               p'.(ac) = (read_mem' p.(mem) n) -> lang_semantics p p'
  | asm_store: forall n, read_instr p (Store n) -> p.(pc) + 1 = p'.(pc) ->
               p.(prog) = p'.(prog) -> p.(ac) = p'.(ac) ->
               p.(ac) = read_mem' p'.(mem) n -> lang_semantics p p'.
