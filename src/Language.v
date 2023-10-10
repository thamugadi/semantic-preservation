Module Language.
Require Import List.
Import ListNotations.

Inductive lang_instr : Type :=
  | PtrInc : lang_instr
  | PtrDec : lang_instr
  | Inc : lang_instr
  | Dec : lang_instr
  | Jump : lang_instr
  | Ret : lang_instr
  | Halt : lang_instr.
Definition lang_program := list lang_instr.

Record lang_state : Type := mkState
{ 
  prog : lang_program;
  pc : nat;
  ptr : nat;
}.

Fixpoint read_instr' (prog : lang_program) (pc : nat) : lang_instr :=
  match prog, pc with
  | [], _ => Halt
  | i :: _, 0 => i
  | _ :: t, S pc' => read_instr' t pc'
  end.

Inductive read_instr (p : lang_state) (i : lang_instr) : Prop  :=
  | ri : read_instr' p.(prog) p.(pc) = i -> read_instr p i.

(* Small-step operational semantics for our source language.*)

Inductive lang_semantics (p : lang_state) (p' : lang_state) : Prop :=
  | lang_ptr_inc : read_instr p PtrInc -> p.(ptr) + 1 = p'.(ptr) ->
                   p.(pc) + 1 = p'.(pc) -> lang_semantics p p'. 
End Language.