Require Import List.
Import List.ListNotations.
Require Import Program.Equality.
Require Import Common.
Module Assembly.

Inductive instr : Type :=
  | AddPtr : nat -> instr
  | SubPtr : nat -> instr
  | Add : nat -> instr
  | Sub : nat -> instr
  | Jump : nat -> instr
  | Skip : instr
  | Halt : instr
  | UJUMP : instr (* unlinked *)
  | URET : instr (* unlinked *).

Definition program := list instr.
Record state: Type := mkState
{ 
  prog : program;
  mem : list nat;
  pc : nat;
  ac : nat;
}.

Definition read_instr (p : state) (i : instr) :=
  Common.lookup (prog p) (pc p) i.

(* Small-step operational semantics for our target language.*)
(*list_eq_except*)
Inductive semantics (p p' : state) : Prop :=
  | add_ptr : forall imm, read_instr p (AddPtr imm) ->
          pc p + 1 = pc p' -> prog p = prog p' -> ac p = ac p' ->
          Common.list_eq_except (mem p) (mem p') [ac p] -> (forall x,
          Common.lookup (mem p) (ac p) x -> Common.lookup (mem p') (ac p') (x+imm)) ->
          semantics p p'
  | sub_ptr : forall imm, read_instr p (SubPtr imm) ->
          pc p + 1 = pc p' -> prog p = prog p' -> ac p = ac p' ->
          Common.list_eq_except (mem p) (mem p') [ac p] -> (forall x,
          Common.lookup (mem p) (ac p) x -> Common.lookup (mem p') (ac p') (x-imm)) ->
          semantics p p'
  | add : forall imm, read_instr p (Add imm) ->
          pc p + 1 = pc p' -> prog p = prog p' -> mem p = mem p' ->
          ac p' = ac p + imm -> semantics p p'
  | sub : forall imm, read_instr p (Sub imm) ->
          pc p + 1 = pc p' -> prog p = prog p' -> mem p = mem p' ->
          ac p' = ac p - imm -> semantics p p'
  | jump: forall addr, read_instr p (Jump addr) ->
          prog p = prog p' -> mem p = mem p' -> ac p = ac p' ->
          pc p' = addr -> semantics p p'
  | skipnz:read_instr p Skip -> prog p = prog p' -> mem p = mem p' ->
           ac p = ac p' -> Common.lookup (mem p') (ac p') 0 -> pc p' = pc p + 2 -> semantics p p'
  | skipz: read_instr p Skip -> prog p = prog p' -> mem p = mem p' ->
           ac p = ac p' -> Common.lookup (mem p') (ac p') 0 -> pc p' = pc p + 1 -> semantics p p'.
End Assembly.