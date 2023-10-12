Require Import Common.
Require Import Language.
Require Import Assembly.

Require Import List.
Import ListNotations.
Require Import PeanoNat.
Import Nat.
Module Compiler.

Fixpoint matched' (p : Language.program) (c : nat) : bool :=
  match c with
  | 0 => false
  | _ => match p with
    | [] => c =? 1
    | Language.Jump :: l => matched' l (c+1)
    | Language.Ret  :: l => matched' l (c-1)
    | _ :: l => matched' l c
    end
  end.
Definition matched (p : Language.program) : bool := matched' p 1.

(* won't compute new addresses *)
Fixpoint compile'' (p : Language.program): (Assembly.program) :=
  match p with
  | [] => []
  | Language.PtrInc :: t => (Assembly.Add 1) :: compile'' t
  | Language.PtrDec :: t => (Assembly.Sub 1) :: compile'' t
  | Language.Inc :: t =>  Assembly.Swap   ::
                          Assembly.Mov    ::
                          Assembly.Add 1  ::
                          Assembly.Zero   ::
                          Assembly.Swap   :: compile'' t
  | Language.Dec :: t =>  Assembly.Swap   ::
                          Assembly.Mov    ::
                          Assembly.Sub 1  ::
                          Assembly.Zero   ::
                          Assembly.Swap   :: compile'' t
  | Language.Jump :: t => Assembly.Skip   ::
                          Assembly.Jump 0 :: compile'' t
  | Language.Ret :: t =>  Assembly.Skip   ::
                          Assembly.Jump 1 :: compile'' t
  | Language.Halt :: t => Assembly.Halt   :: compile'' t
  end.

Fixpoint new_pc' (p : Language.program) (pc c c' : nat) : nat :=
  match p with
  | [] => 0
  | Language.PtrInc :: t => if c =? pc then c' else new_pc' t pc (c+1) (c'+1)
  | Language.PtrDec :: t => if c =? pc then c' else new_pc' t pc (c+1) (c'+1)
  | Language.Inc :: t =>    if c =? pc then c' else new_pc' t pc (c+1) (c'+5)
  | Language.Dec :: t =>    if c =? pc then c' else new_pc' t pc (c+1) (c'+5)
  | Language.Jump :: t =>   if c =? pc then c' else new_pc' t pc (c+1) (c'+2)
  | Language.Ret :: t =>    if c =? pc then c' else new_pc' t pc (c+1) (c'+2)
  | Language.Halt :: t =>   if c =? pc then c' else new_pc' t pc (c+1) (c'+1)
  end.

Definition new_pc (p : Language.program) (pc : nat) : nat := new_pc' p pc 0 0.

Definition safe_head (p : list nat) : nat :=
  match p with
  | [] => 0
  | h :: l => h
  end. (* no risk of unmatched jump / ret, thanks to Language.matching_ret *)

Fixpoint link_ret' (p : Assembly.program) (pos : nat) (c : list nat) : Assembly.program :=
  match p with
  | [] => []
  | Assembly.Jump 0 :: t => Assembly.Jump 0 :: link_ret' t (pos+1) (pos::c)
  | Assembly.Jump 1 :: t => Assembly.Jump (safe_head c) :: link_ret' t (pos+1) (tail c)
  | i :: t => i :: link_ret' t (pos+1) c 
  end.

Definition link_ret (p : Assembly.program) : Assembly.program := link_ret' p 0 [].

Fixpoint get_index (l: Assembly.program) (start_idx: nat) : option nat :=
  match l with
  | [] => None
  | Assembly.Jump 1 :: t => Some start_idx
  | _ :: t => get_index t (start_idx + 1)
  end.

Fixpoint link_jump' (l: Assembly.program) (idx : nat) : Assembly.program :=
  match l with
  | [] => []
  | h :: t => match h with
              | Assembly.Jump 0 => match get_index t (idx + 1) with
                                   | Some i => Assembly.Jump i :: link_jump' t (idx + 1)
                                   | None   => h :: link_jump' t (idx + 1)
                                   end
              | _ => h :: link_jump' t (idx + 1)
              end
  end.

Definition link_jump (l : Assembly.program) : Assembly.program := link_jump' l 0.

Definition link (l : Assembly.program) : Assembly.program := link_jump (link_ret l).

Definition compile' (p : Language.state) : Assembly.state :=
  Assembly.mkState (link (compile'' p.(Language.prog))) p.(Language.mem)
                   (new_pc p.(Language.prog) p.(Language.pc)) p.(Language.ptr) 0.

Definition compile (p : Language.state) : option Assembly.state :=