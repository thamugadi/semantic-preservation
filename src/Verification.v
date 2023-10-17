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
  forall p p' q, Compiler.compile p q -> eval p p' ->
              Language.read_instr p Language.PtrInc ->
              exists q', (eval' q q' /\ Assembly.read_instr q' 
              (first_comp_instr (Language.read_instr' p'.(Language.prog) p'.(Language.pc)))).   
Proof.
Admitted.
Theorem sequence_comp_inc :
  forall p p' q, Compiler.compile p q -> eval p p' ->
              Language.read_instr p Language.Inc ->
              exists q'1, (eval' q q'1 /\ Assembly.read_instr q'1 Assembly.Swap) /\
              exists q'2, (eval' q'1 q'2 /\ Assembly.read_instr q'2 Assembly.Load) /\
              exists q'3, (eval' q'2 q'3 /\ Assembly.read_instr q'3 (Assembly.Add 1)) /\
              exists q'4, (eval' q'3 q'4 /\ Assembly.read_instr q'4 Assembly.Store) /\
              exists q'5, (eval' q'4 q'5 /\ Assembly.read_instr q'5 Assembly.Zero) /\
              exists q'6, (eval' q'5 q'6 /\ Assembly.read_instr q'6 Assembly.Swap) /\
              exists q', (eval' q'6 q' /\ Assembly.read_instr q'
              (first_comp_instr (Language.read_instr' p'.(Language.prog) p'.(Language.pc)))).   
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
      assert (q.(Assembly.pc) = Compiler.new_pc (p.(Language.prog)) (p.(Language.pc)) /\
              q.(Assembly.ac) = p.(Language.ptr) /\
              q.(Assembly.mem) = p.(Language.mem) /\
              q.(Assembly.b) = 0).
      apply comp_newstate.
      assumption.
      assert (q'.(Assembly.pc) = Compiler.new_pc (p'.(Language.prog)) (p'.(Language.pc)) /\
              q'.(Assembly.ac) = p'.(Language.ptr) /\
              q'.(Assembly.mem) = p'.(Language.mem) /\
              q'.(Assembly.b) = 0).
      {  
        apply comp_newstate.
        apply Compiler.comp_r. 
        assumption.
        assumption.
      }
      destruct H7. destruct H9. destruct H10.
      destruct H8. destruct H12. destruct H13.
      assert (Assembly.read_instr q' (first_comp_instr
               (Language.read_instr' p'.(Language.prog) p'.(Language.pc)))).
      {
        apply first_instr_comp with (p := p').
        apply Compiler.comp_r.
        assumption.
        assumption.
        apply Language.ri.
        reflexivity.
      }
      remember ((first_comp_instr (Language.read_instr'
               (Language.prog p') (Language.pc p')))) as i.
      
      (* todo: prove sufficient conditions 
               for eval'+ q q' to hold, instead of the stronger eval' q q'*)
      
      
Admitted. (* to be done. *)

End Verification.