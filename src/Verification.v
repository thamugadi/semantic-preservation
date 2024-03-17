Require Import Common.
Require Import Language.
Require Import Assembly.
Require Import Simulation.
Require Import Compiler.
Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Program.Equality.
Require Import PeanoNat.

From Hammer Require Import Hammer.
From Hammer Require Import Tactics.

Import Nat.
Module Verification.
(*
Inductive IndexEquiv : list Assembly.instr -> nat -> nat -> Prop := *)


Lemma link_stable : forall p ind i,
                    (i <> Assembly.UJUMP /\ i <> Assembly.URET) ->
                    Common.lookup p ind i -> 
                    Common.lookup (Compiler.link p) ind i.
Admitted.

Lemma lm : forall a p, Compiler.compile'' (a :: p) = [] -> False.
Admitted.
Lemma comp_instr : forall prog pc i,
                   Common.lookup prog pc i ->
                   Common.lookup (Compiler.compile'' prog) 
                                 (Compiler.compile_index prog pc)
                                 (Compiler.comp_first i).
Proof.
Admitted.

Theorem th : Simulation.plus_forward_sim Compiler.compile 
             Language.semantics Assembly.semantics.
Proof.
  unfold Simulation.plus_forward_sim.
  intros.
  inversion H.
  assert (forall q2, Assembly.semantics q q2 -> Assembly.prog q2 = Assembly.prog q).
  ssimpl.
  destruct H0 eqn:T; exists (Assembly.mkState
            (Assembly.prog q)
            (Assembly.mem (Compiler.compile' p'))
            (Assembly.pc (Compiler.compile' p'))
            (Assembly.ac (Compiler.compile' p'))); split; qsimpl;
  try (apply Compiler.comp;
  unfold Compiler.compile'; rewrite e; reflexivity); clear H2.
  - apply Common.t_base.
    apply Assembly.add with (imm := 1).
    + unfold Language.read_instr, Assembly.read_instr in *.
      qsimpl.
      assert (Assembly.Add 1 = Compiler.comp_first Language.PtrInc).
      now reflexivity.
      admit.
    + admit.
    + admit.
    + admit.
Admitted.

End Verification.