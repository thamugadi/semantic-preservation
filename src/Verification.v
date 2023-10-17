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

Theorem match_preserve : 
  forall p p', Language.semantics p p' ->
               Compiler.matched (Language.prog p) ->
               Compiler.matched (Language.prog p').
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
      assert (Assembly.read_instr q (Assembly.Add 1)).
      (* todo: prove sufficient conditions 
               for eval'+ q q' to hold, instead of the stronger eval' q q'*)
      
      
Admitted. (* to be done. *)

End Verification.