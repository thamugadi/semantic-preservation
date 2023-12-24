Require Import Common.
Require Import Language.
Require Import Assembly.
Require Import Simulation.
Require Import Compiler.
Require Import Lia.
Require Import Vector.
Import Vector.VectorNotations.
Require Import Program.Equality.
Require Import PeanoNat.

From Hammer Require Import Hammer.
From Hammer Require Import Tactics.

Import Nat.
Module Verification.

Definition eval {n m} := @Language.semantics n m.
Definition eval' {n m} := @Assembly.semantics n m.
Check eval.
Lemma comp_len_eq : forall n m p p', eval p p' -> @Compiler.comp_len n (@Language.prog n m p) = @Compiler.comp_len n (@Language.prog n m p').
Proof.
  intros.
  assert (p.(Language.prog) = p'.(Language.prog)).
  + inversion H; assumption.
  + inversion H0.
    reflexivity.
Defined.

Definition comp_len_f {n n' m p p'} (H : eval p p') (q : @Assembly.state (@Compiler.comp_len n (@Language.prog n m p')) n') : @Assembly.state (@Compiler.comp_len n (@Language.prog n m p)) n'.
Proof.
  assert (@Compiler.comp_len n (@Language.prog n m p) = @Compiler.comp_len n (@Language.prog n m p')).
  - apply comp_len_eq.
    assumption.
  - rewrite H0.
    exact q.
Defined.
  
Lemma match_tr {n m} : forall p p', Compiler.matched (n := n) (Language.prog p) -> eval p p' -> Compiler.matched (Language.prog p' (m := m)).
Proof.
  intros.
  assert (Language.prog p = Language.prog p').
  - inversion H0; assumption.
  - rewrite <- H1.
    assumption.
Qed.

Lemma comp_link_prog {n m} : forall p HA HA1 q, Compiler.compile_link p HA HA1 = q -> q.(Assembly.prog) = Compiler.link (@Compiler.compile'' n p.(@Language.prog n m)).
Proof.
  intros.
  rewrite <- H.
  assert (Assembly.prog
  {|
    Assembly.prog := Compiler.link (Assembly.prog (Compiler.compile' p HA HA1));
    Assembly.mem := Assembly.mem (Compiler.compile' p HA HA1);
    Assembly.pc := Assembly.pc (Compiler.compile' p HA HA1);
    Assembly.ac := Assembly.ac (Compiler.compile' p HA HA1);
    Assembly.b := Assembly.b (Compiler.compile' p HA HA1)
  |} = Compiler.link (Assembly.prog (Compiler.compile' p HA HA1))).
  now reflexivity.
  unfold Compiler.compile_link.
  rewrite H0.
  f_equal.
Qed.

Definition len_asm {n} (i : @Assembly.instr n) : nat :=
  match i with
  | Assembly.Add 1 => 1
  | Assembly.Sub 1 => 1
  | Assembly.Swap => 6
  | Assembly.Skip => 2
  | Assembly.Halt => 1
  | _ => 0
  end.

Fixpoint to_nat {n} (x : Fin.t n) : nat.
Proof.
  destruct x eqn:H.
  - exact 0.
  - apply plus.
    + exact 1.
    + apply to_nat with (n := n).
      exact t0.
Defined.


Theorem comp_correct {n : nat} :
    forall p q, Compiler.compile p q -> 
    forall p' (E : eval p p'), 
    exists q', Compiler.compile p' q' /\ (Common.plus eval') q (comp_len_f (n := n) (n' := n) E q').
Proof.
  intros.
  assert (n <> 0).
  inversion H. assumption.
  exists (Compiler.compile_link p' H0 H0).
  split.
  - apply Compiler.comp_r with (H := H0) (H1 := H0).
    + assert (Compiler.matched (Language.prog p)).
      inversion H.
      assumption.
      apply match_tr with (p := p); assumption.
    + reflexivity. 
  - (unfold comp_len_f; unfold eq_rec_r; unfold eq_rec; unfold eq_rect).
    ssimpl.
    + apply Common.t_base.
      apply Assembly.add with (n' := 1).
      * admit. (*requires a general lemma*)
      * ssimpl. (*requires a general lemma*) admit.
      * now reflexivity. (*easy*)
      * now reflexivity.
      * admit. (*probably will be deduced from the general lemma for (1)*)
      * admit. (*same*)
Admitted.

End Verification.