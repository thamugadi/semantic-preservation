Require Import Common.
Require Import Language.
Require Import Assembly.
Require Import Simulation.
Require Import Compiler.
Require Import List.
Import ListNotations.
Require Import PeanoNat.
Import Nat.
Module Verification.
Inductive compile : Language.state -> Assembly.state -> Prop :=
  | comp_r : forall p a, Compiler.compile p = Some a -> compile p a.

Theorem comp_correct : 
  Simulation.plus_forward_sim compile Language.semantics Assembly.semantics.
Proof.
  unfold Simulation.plus_forward_sim.
  intros.
Admitted. (* to be done. *)

End Verification.