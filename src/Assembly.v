Require Import List.
Import ListNotations.
Require Import Common.
Require Import PeanoNat.
Import Nat.
Module Assembly.

Inductive instr : Type :=
  | Load : nat -> instr
  | Store : nat -> instr
  | Add : nat -> instr
  | Sub : nat -> instr
  | Jump : nat -> instr
  | Skip : instr
  | Halt : instr.

Definition program := list instr.

Record state : Type := mkState
{ 
  prog : program;
  mem : list nat;
  pc : nat;
  ac : nat;
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
  | mi : read_mem' p.(mem) p.(ac) = n -> read_mem p n.

Inductive mem_diff (m : list nat) (m' : list nat) (ac : nat) : Prop :=
  | c_diff : Common.take ac m = Common.take ac m' ->
               Common.drop (ac+1) m = Common.drop (ac+1) m' ->
               mem_diff m m' ac.

(* Small-step operational semantics for our target language.*)

Inductive semantics (p : state) (p' : state) : Prop :=
  | load : forall n, read_instr p (Load n) -> p.(pc) + 1 = p'.(pc) ->
               p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
               p'.(ac) = (read_mem' p.(mem) n) -> semantics p p'
  | store: forall n, read_instr p (Store n) -> p.(pc) + 1 = p'.(pc) ->
               p.(prog) = p'.(prog) -> p.(ac) = p'.(ac) ->
               p.(ac) = read_mem' p'.(mem) n ->
               mem_diff p.(mem) p'.(mem) p.(ac) -> semantics p p'
  | add : forall n, read_instr p (Add n) -> p.(pc) + 1 = p'.(pc) ->
              p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
              p'.(ac) = p.(ac) + n -> semantics p p'
  | sub : forall n, read_instr p (Sub n) -> p.(pc) + 1 = p'.(pc) ->
              p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
              p'.(ac) = p.(ac) - n -> semantics p p'
  | jump : forall n, read_instr p (Jump n) -> p.(prog) = p'.(prog) ->
               p.(ac) = p'.(ac) -> p.(mem) = p'.(mem) -> p'.(pc) = n ->
               semantics p p'
  | skipz: read_instr p (Skip) -> p.(prog) = p'.(prog) ->
               p.(mem) = p'.(mem) -> p.(ac) = p'.(ac) ->
               read_mem p 0 -> p'.(pc) = p.(pc) + 2 -> semantics p p'
  | skipnz: read_instr p (Skip) -> p.(prog) = p'.(prog) ->
                p.(mem) = p'.(mem) -> p.(ac) = p'.(ac) ->
                ~ (read_mem p 0) -> p'.(pc) = p.(pc) + 1 -> semantics p p'.

End Assembly.