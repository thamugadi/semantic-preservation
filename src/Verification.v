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
Import Nat.
Module Verification.

Definition eval {n} := @Language.semantics n.
Definition eval' {n} := @Assembly.semantics n 512.

Lemma comp_len_eq : forall n p p', eval p p' -> @Compiler.comp_len n (@Language.prog n p) = @Compiler.comp_len n (@Language.prog n p').
Proof.
  intros.
  assert (p.(Language.prog) = p'.(Language.prog)).
  + inversion H; assumption.
  + inversion H0.
    reflexivity.
Defined.

Definition comp_len_f {n p p'} (H : eval p p') (q : @Assembly.state (@Compiler.comp_len n (@Language.prog n p')) 512) : @Assembly.state (@Compiler.comp_len n (@Language.prog n p)) 512.
Proof.
  assert (@Compiler.comp_len n (@Language.prog n p) = @Compiler.comp_len n (@Language.prog n p')).
  - apply comp_len_eq.
    assumption.
  - rewrite H0.
    exact q.
Defined.
Definition comp_len_f' {n p p'} (H : eval p p') (q : @Assembly.state (@Compiler.comp_len n (@Language.prog n p)) 512) : @Assembly.state (@Compiler.comp_len n (@Language.prog n p')) 512.
Proof.
  assert (@Compiler.comp_len n (@Language.prog n p) = @Compiler.comp_len n (@Language.prog n p')).
  - apply comp_len_eq.
    assumption.
  - rewrite <- H0.
    exact q.
Defined.
  
Lemma match_tr {n} : forall p p', Compiler.matched (n := n) (Language.prog p) -> eval p p' -> Compiler.matched (Language.prog p').
Proof.
  intros.
  assert (Language.prog p = Language.prog p').
  - inversion H0; assumption.
  - rewrite <- H1.
    assumption.
Qed.

Lemma comp_link_prog {n : nat} : forall p HA q, Compiler.compile_link p HA = q -> q.(Assembly.prog) = Compiler.link (@Compiler.compile'' n p.(Language.prog)).
Proof.
  intros.
  rewrite <- H.
  assert (Assembly.prog
  {|
    Assembly.prog := Compiler.link (Assembly.prog (Compiler.compile' p HA));
    Assembly.mem := Assembly.mem (Compiler.compile' p HA);
    Assembly.pc := Assembly.pc (Compiler.compile' p HA);
    Assembly.ac := Assembly.ac (Compiler.compile' p HA);
    Assembly.b := Assembly.b (Compiler.compile' p HA)
  |} = Compiler.link (Assembly.prog (Compiler.compile' p HA))).
  now reflexivity.
  unfold Compiler.compile_link.
  rewrite H0.
  f_equal.
Qed.


Lemma comp_instr {n : nat} : forall (x : Fin.t n) (p : Language.program n), Compiler.compile_first p[@x] = (Compiler.compile'' p)[@Compiler.compile_index p x].
Proof.
Admitted. (* to be done (+ another one for linking) *)

Theorem comp_correct {n : nat} :
    forall p q, Compiler.compile p q -> 
    forall p' (E : eval p p'), 
    exists q', Compiler.compile p' q' /\ (Common.plus eval') q (comp_len_f (n := n) E q').
Proof.
  intros.
  assert (n <> 0).
  inversion H. assumption.
  exists (Compiler.compile_link p' H0).
  split.
  - apply Compiler.comp_r with (H := H0).
    + assert (Compiler.matched (Language.prog p)).
      inversion H.
      assumption.
      apply match_tr with (p := p); assumption.
    + reflexivity.
  - destruct E; remember (Compiler.compile_link p' H0) as q';
    inversion H;
    assert (Assembly.prog q = (Compiler.compile_link p H0).(Assembly.prog));
    assert (Assembly.to_nat (Assembly.pc q) = Assembly.to_nat (Compiler.compile_index (Language.prog p) (Language.pc p)));
    assert (Assembly.ac q = Fin.F1);
    assert (Assembly.b q = Language.ptr p); (try (inversion H3; now reflexivity)). (*other global assertions (on q') to be added*)
    + apply Common.t_base.
      
    (*todo: assert a corollary of the comp_instr lemma*)

Admitted.

End Verification.