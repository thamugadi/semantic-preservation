Require Import Common.
Require Import Language.
Require Import Assembly.
Require Import Simulation.
Require Import Compiler.
Require Import List.
Require Import Lia.
Import ListNotations.
Require Import PeanoNat.
Import Nat.
Module Verification.
Definition eval := Language.semantics.
Definition eval' := Assembly.semantics.

Theorem comp_newstate :
  forall p q, Compiler.compile p q ->
              q.(Assembly.pc) = Compiler.new_pc (p.(Language.prog)) (p.(Language.pc)) /\
              q.(Assembly.ac) = p.(Language.ptr) /\
              q.(Assembly.mem) = p.(Language.mem) /\
              q.(Assembly.b) = 0.
Proof.
Admitted.

Theorem match_preserve : 
  forall p p', Language.semantics p p' ->
               Compiler.matched (Language.prog p) ->
               Compiler.matched (Language.prog p').
Proof.
Admitted.

Definition first_comp_instr (i : Language.instr) : Assembly.instr :=
  match i with
  | Language.PtrInc => Assembly.Add 1
  | Language.PtrDec => Assembly.Sub 1
  | Language.Inc => Assembly.Swap
  | Language.Dec => Assembly.Swap
  | Language.Jump => Assembly.Skip
  | Language.Ret => Assembly.Skip
  | Language.Halt => Assembly.Halt
  end.

Theorem first_instr_comp : forall p q i, Compiler.compile p q ->
                           Language.read_instr p i ->
                           Assembly.read_instr q (first_comp_instr i).
Proof.
Admitted.

Theorem sequence_comp_ptrinc :
  forall p p' q q', Compiler.compile p q -> eval p p' -> Compiler.compile p' q' ->
              Language.read_instr p Language.PtrInc ->
              eval' q q'.
Proof.
Admitted.
Theorem sequence_comp_ptrdec :
  forall p p' q q', Compiler.compile p q -> eval p p' -> Compiler.compile p' q' ->
              Language.read_instr p Language.PtrDec ->
              eval' q q'.
Proof.
Admitted.
Theorem sequence_comp_inc :
  forall p p' q q', Compiler.compile p q -> eval p p' -> Compiler.compile p' q' ->
              Language.read_instr p Language.Inc ->
              exists q'1, (eval' q q'1) /\
              exists q'2, (eval' q'1 q'2) /\
              exists q'3, (eval' q'2 q'3) /\
              exists q'4, (eval' q'3 q'4) /\
              exists q'5, (eval' q'4 q'5) /\
              exists q'6, (eval' q'5 q'6) /\
              eval' q'6 q'.
Proof.
Admitted.
Theorem sequence_comp_dec :
  forall p p' q q', Compiler.compile p q -> eval p p' -> Compiler.compile p' q' ->
              Language.read_instr p Language.Dec ->
              exists q'1, (eval' q q'1) /\
              exists q'2, (eval' q'1 q'2) /\
              exists q'3, (eval' q'2 q'3) /\
              exists q'4, (eval' q'3 q'4) /\
              exists q'5, (eval' q'4 q'5) /\
              exists q'6, (eval' q'5 q'6) /\
              eval' q'6 q'.
Proof.
Admitted.
Theorem sequence_comp_jump :
  forall p p' q q', Compiler.compile p q -> eval p p' -> Compiler.compile p' q' ->
              Language.read_instr p Language.Jump ->
              exists q'1, (eval' q q'1) /\
              exists q'2, (eval' q'1 q'2) /\
              eval' q'2 q'.
Proof.
Admitted.
Theorem sequence_comp_ret :
  forall p p' q q', Compiler.compile p q -> eval p p' -> Compiler.compile p' q' ->
              Language.read_instr p Language.Ret ->
              exists q'1, (eval' q q'1) /\
              exists q'2, (eval' q'1 q'2) /\
              eval' q'2 q'.
Proof.
Admitted.
Theorem comp_correct : 
  Simulation.plus_forward_sim Compiler.compile eval eval'.
Proof.
  unfold Simulation.plus_forward_sim, eval, eval'.
  intros p q compileH p' evalH.
  assert (Compiler.matched (Language.prog p')).
  apply match_preserve with (p := p).
  unfold eval in evalH.
  assumption.
  inversion compileH.
  assumption.
  induction evalH.
  - exists (Compiler.compile' p').
    split.
    + apply Compiler.comp_r.
      assumption.
      reflexivity.
    + inversion compileH.
      remember (Compiler.compile' p') as q'.
      
      (* todo: prove sufficient conditions 
               for eval'+ q q' to hold, instead of the stronger eval' q q'*)
      
      
Admitted. (* to be done. *)

End Verification.