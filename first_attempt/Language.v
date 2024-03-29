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

Record state {n m : nat} : Type := mkState
{ 
  prog : program n;
  mem : t nat m;
  pc : Fin.t n;
  ptr : Fin.t m;
}.

Definition read_instr' {n} (prog : program n) (pc : Fin.t n) : instr :=
 prog[@pc].

Inductive read_instr {n m} (p : state) (i : instr) : Prop  :=
  | ri : read_instr' p.(prog n m) p.(pc n m) = i -> read_instr p i.

Definition read_mem' {m} (mem : t nat m) (ptr : Fin.t m) : nat := mem[@ptr].

Inductive read_mem {n m} (p : state) (e : nat) : Prop  :=
  | mi : read_mem' p.(mem n m) p.(ptr n m) = e -> read_mem p e.


Inductive mem_diff {m} (m1 : t nat m) (m2 : t nat m) (x : Fin.t m) : Prop :=
  | md : (forall i, i <> x -> m2[@i] = m1[@i]) -> mem_diff m1 m2 x. 


Definition option_inc (i : option nat) : option nat :=
  match i with
  | None => None
  | Some a => Some (a + 1)
  end.

Fixpoint matching_ret' {n} (l : t instr n) (idx : nat) (c c' : nat) :
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

Fixpoint matching_jump' {n} (l : t instr n) (idx : nat) (c : nat) 
                        (c' : option nat) : option nat :=
  match l with
  | [] => None
  | Jump :: h => if c =? idx then None else matching_jump' h idx (c+1) (Some c)
  | Ret :: h => if c =? idx then (option_inc c') else None
  | _ :: h => if c =? idx then None else matching_jump' h idx (c+1) c'
  end.

Inductive matching_jump {n} (p : program n) (x : Fin.t n) (x' : Fin.t n) : Prop :=
  | mj : matching_jump' p (Common.to_nat x) 0 None = Some (Common.to_nat x') -> matching_jump p x x'.
Inductive matching_ret {n} (p : program n) (x : Fin.t n) (x' : Fin.t n): Prop :=
  | mr : matching_ret' p (Common.to_nat x) 0 0 = Some (Common.to_nat x') -> matching_ret p x x'.

(*Some cases will not be accepted for compilation anyway, like unmatched jumps.*)
(* Small-step operational semantics for our source language.*)

Inductive semantics {n m} (p : state) (p' : state) : Prop :=
  | ptr_inc : read_instr p PtrInc ->  Common.to_nat p.(ptr) + 1 = Common.to_nat p'.(ptr) ->
                   Common.to_nat p.(pc n m) + 1 = Common.to_nat p'.(pc)-> p.(prog) = p'.(prog) ->
                   p.(mem) = p'.(mem) -> semantics p p'
  | ptr_dec : read_instr p PtrDec -> Common.to_nat p.(ptr) - 1 = Common.to_nat p'.(ptr) ->
                    Common.to_nat p.(pc) +1 = Common.to_nat p'.(pc)-> p.(prog) = p'.(prog) ->
                   p.(mem) = p'.(mem) -> semantics p p'
  | inc : read_instr p Inc -> p.(ptr) = p'.(ptr) ->
               Common.to_nat p.(pc) +1 = Common.to_nat p'.(pc)-> p.(prog) = p'.(prog) ->
               mem_diff p.(mem) p'.(mem) p.(ptr) ->
               p.(mem)[@p.(ptr)] + 1 = p'.(mem)[@p.(ptr)] ->
               semantics p p'
  | dec : read_instr p Dec -> p.(ptr) = p'.(ptr) ->
               Common.to_nat p.(pc) +1 = Common.to_nat p'.(pc)-> p.(prog) = p'.(prog) ->
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
                   Common.to_nat p.(pc) + 1 = Common.to_nat p'.(pc)-> semantics p p'
  | ret_z :  read_instr p Ret -> p.(ptr) = p'.(ptr) ->
                  p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
                  matching_jump p.(prog) p.(pc) p'.(pc) -> read_mem p 0 ->
                  semantics p p'
  | ret_nz : read_instr p Ret -> p.(ptr) = p'.(ptr) ->
                  p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
                  ~ (read_mem p 0) ->
                  Common.to_nat p.(pc) +  1 = Common.to_nat p'.(pc) -> semantics p p'.
End Language.