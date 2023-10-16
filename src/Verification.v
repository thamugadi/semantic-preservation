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
Inductive compile : Language.state -> Assembly.state -> Prop :=
  | comp_r : forall p a, Compiler.compile p = Some a -> compile p a.

Definition eval := Language.semantics.
Definition eval' := Assembly.semantics.

Theorem comp_correct : 
  Simulation.plus_forward_sim compile eval eval'.
Proof.
  unfold Simulation.plus_forward_sim.
  induction p.

    
Admitted. (* to be done. *)

End Verification.