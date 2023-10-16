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
Theorem ptrinc_comp :
  forall p q, Compiler.compile p q -> 
              Language.read_instr p Language.PtrInc ->
              Assembly.read_instr q (Assembly.Add 1).
Proof.
Admitted.
Theorem ptrdec_comp :
  forall p q, Compiler.compile p q -> 
              Language.read_instr p Language.PtrDec ->
              Assembly.read_instr q (Assembly.Sub 1).
Proof.
Admitted.
Theorem inc_comp :
  forall p q, Compiler.compile p q -> 
              Language.read_instr p Language.Inc ->
              Assembly.read_instr q (Assembly.Swap).
Proof.
Admitted.
Theorem dec_comp :
  forall p q, Compiler.compile p q -> 
              Language.read_instr p Language.Dec ->
              Assembly.read_instr q (Assembly.Swap).
Proof.
Admitted.
Theorem jump_comp :
  forall p q, Compiler.compile p q -> 
              Language.read_instr p Language.Jump ->
              Assembly.read_instr q (Assembly.Skip).
Proof.
Admitted.
Theorem ret_comp :
  forall p q, Compiler.compile p q -> 
              Language.read_instr p Language.Ret ->
              Assembly.read_instr q (Assembly.Skip).
Proof.
Admitted.
Theorem comp_correct : 
  Simulation.plus_forward_sim Compiler.compile eval eval'.
Proof.
  unfold Simulation.plus_forward_sim.
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
      assert (Assembly.read_instr q (Assembly.Add 1)).

Admitted. (* to be done. *)

End Verification.