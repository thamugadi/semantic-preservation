Require Import Vector.
Import Vector.VectorNotations.
Require Import Program.Equality.
Require Import PeanoNat.
Require Import Common.
Require Import Lia.
Module Language.
Inductive instr : Type :=
  | PtrInc : instr
  | PtrDec : instr
  | Inc : instr
  | Dec : instr
  | Jump : instr
  | Ret : instr
  | Halt : instr.
Definition program (n : nat) := t instr n.

Record state {n : nat} : Type := mkState
{ 
  prog : program n;
  mem : t nat 512;
  pc : Fin.t n;
  ptr : Fin.t 512;
}.

Definition read_instr' {n} (prog : program n) (pc : Fin.t n) : instr := prog[@pc].

Inductive read_instr {n} (p : state) (i : instr) : Prop  :=
  | ri : read_instr' p.(prog n) p.(pc n) = i -> read_instr p i.

Definition read_mem' (mem : t nat 512) (ptr : Fin.t 512) : nat := mem[@ptr].

Inductive read_mem {n} (p : state) (e : nat) : Prop  :=
  | mi : read_mem' p.(mem n) p.(ptr n) = e -> read_mem p e.

Fixpoint to_nat {n} (x : Fin.t n) : nat.
Proof.
  destruct x eqn:H.
  - exact 0.
  - apply plus.
    + exact 1.
    + apply to_nat with (n := n).
      exact t.
Defined.

Inductive mem_diff {m} (m1 : t nat m) (m2 : t nat m) (x : Fin.t m) : Prop :=
  | md : (forall i, i <> x -> m2[@i] = m1[@i]) -> mem_diff m1 m2 x. 

Fixpoint matching_ret' {n} (l : t instr n) (idx : nat) (c c' : nat) : option nat :=
  match l with
  | [] => None
  | i :: h => if c' <=? idx then matching_ret' h idx c (c'+1) else
    match i with
    | Jump => matching_ret' h idx (c+1) (c'+1)
    | Ret => if c =? 0 then Some c' else matching_ret' h idx (c-1) (c'+1)
    | _ => matching_ret' h idx c (c'+1)
  end
end.

Fixpoint matching_jump' {n} (l : t instr n) (idx : nat) (c : nat) (c' : option nat) : option nat :=
  match l with
  | [] => None
  | Jump :: h => if c =? idx then None else matching_jump' h idx (c+1) (Some c)
  | Ret :: h => if c =? idx then c' else None
  | _ :: h => if c =? idx then None else matching_jump' h idx (c+1) c'
  end.

Inductive matching_jump {n} (p : program n) (x : Fin.t n) (x' : Fin.t n) : Prop :=
  | mj : matching_jump' p (to_nat x) 0 None = Some (to_nat x') -> matching_jump p x x'.
Inductive matching_ret {n} (p : program n) (x : Fin.t n) (x' : Fin.t n): Prop :=
  | mr : matching_ret' p (to_nat x) 0 0 = Some (to_nat x') -> matching_ret p x x'.

(*Some cases will not be accepted for compilation anyway, like unmatched jumps.*)
(* Small-step operational semantics for our source language.*)

Inductive semantics {n} (p : state) (p' : state) : Prop :=
  | ptr_inc : read_instr p PtrInc ->  to_nat p.(ptr) + 1 = to_nat p'.(ptr) ->
                   to_nat p.(pc n) + 1 = to_nat p'.(pc)-> p.(prog) = p'.(prog) ->
                   p.(mem) = p'.(mem) -> semantics p p'
  | ptr_dec : read_instr p PtrDec -> to_nat p.(ptr) - 1 = to_nat p'.(ptr) ->
                    to_nat p.(pc) +1 = to_nat p'.(pc)-> p.(prog) = p'.(prog) ->
                   p.(mem) = p'.(mem) -> semantics p p'
  | inc : read_instr p Inc -> p.(ptr) = p'.(ptr) ->
               to_nat p.(pc) +1 = to_nat p'.(pc)-> p.(prog) = p'.(prog) ->
               mem_diff p.(mem) p'.(mem) p.(ptr) ->
               p.(mem)[@p.(ptr)] + 1 = p'.(mem)[@p.(ptr)] ->
               semantics p p'
  | dec : read_instr p Dec -> p.(ptr) = p'.(ptr) ->
               to_nat p.(pc) +1 = to_nat p'.(pc)-> p.(prog) = p'.(prog) ->
               mem_diff p.(mem) p'.(mem) p.(ptr) ->
               p.(mem)[@p.(ptr)] - 1 = p'.(mem)[@p.(ptr)] ->
               semantics p p'
  | jump_z : read_instr p Jump -> p.(ptr) = p'.(ptr) ->
                  p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
                  read_mem p 0 -> matching_ret p.(prog) p.(pc) p'.(pc) ->
                  semantics p p'
  | jump_nz : read_instr p Jump -> p.(ptr) = p'.(ptr) ->
                   p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
                   ~ (read_mem p 0) ->
                   to_nat p.(pc) + 1 = to_nat p'.(pc)-> semantics p p'
  | ret_z :  read_instr p Ret -> p.(ptr) = p'.(ptr) ->
                  p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
                  matching_jump p.(prog) p.(pc) p'.(pc) -> read_mem p 0 ->
                  semantics p p'
  | ret_nz : read_instr p Ret -> p.(ptr) = p'.(ptr) ->
                  p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
                  ~ (read_mem p 0) ->
                  to_nat p.(pc) +  1 = to_nat p'.(pc) -> semantics p p'.
End Language.