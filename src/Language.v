Require Import List.
Import ListNotations.
Require Import Common.

Module Language.
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
  mem : list nat;
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

(* Small-step operational semantics for our source language.*)
Inductive lang_semantics (p : lang_state) (p' : lang_state) : Prop :=
  | lang_ptr_inc : read_instr p PtrInc -> p.(ptr) + 1 = p'.(ptr) ->
                   p.(pc) + 1 = p'.(pc) -> p.(prog) = p'.(prog) ->
                   p.(mem) = p'.(mem) -> lang_semantics p p' 
  | lang_ptr_dec : read_instr p PtrDec -> p.(ptr) - 1 = p'.(ptr) ->
                   p.(pc) + 1 = p'.(pc) -> p.(prog) = p'.(prog) ->
                   p.(mem) = p'.(mem) -> lang_semantics p p'
  | lang_inc : read_instr p Inc -> length p.(mem) > p.(ptr) ->
               p.(pc) + 1 = p'.(pc) -> p.(prog) = p'.(prog) ->
               mem_diff_p p.(mem) p'.(mem) p.(ptr) -> lang_semantics p p' 
  | lang_dec : read_instr p Dec -> length p.(mem) > p.(ptr) ->
               p.(pc) + 1 = p'.(pc) -> p.(prog) = p'.(prog) ->
               mem_diff_m p.(mem) p'.(mem) p.(ptr) -> lang_semantics p p'. 
  
End Language.