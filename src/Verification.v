Require Import Common.
Require Import Language.
Require Import Assembly.
Require Import Simulation.
Require Import Compiler.
Require Import Lia.
Require Import List.
Import ListNotations.

From Hammer Require Import Hammer.
From Hammer Require Import Tactics.

Import Nat.
Module Verification.

Lemma lm1 : forall a p, Compiler.compile'' (a :: p) = [] -> False.
Proof.
  intros.
  destruct p;
  destruct a; simpl;
  discriminate.
Qed.

Lemma trv : forall n, n - 0 = n.
Proof. lia. Qed.

Lemma comp_instr_lm : forall p q pc i,
                      Compiler.compile'' p = q ->
                      Common.lookup p pc i ->
                      Common.lookup q (Compiler.compile_index p pc)
                                      (Compiler.comp_first i).
Proof.
  induction p; destruct q; destruct i; intros; try inversion H.
  - exfalso; inversion H0.
  - exfalso; inversion H0.
  - exfalso; inversion H0.
  - exfalso; inversion H0.
  - exfalso; inversion H0.
  - exfalso; inversion H0.
  - exfalso; inversion H0.
  - exfalso; apply lm1 with (a := a) (p := p); assumption.
  - exfalso; apply lm1 with (a := a) (p := p); assumption.
  - exfalso; apply lm1 with (a := a) (p := p); assumption.
  - exfalso; apply lm1 with (a := a) (p := p); assumption.
  - exfalso; apply lm1 with (a := a) (p := p); assumption.
  - exfalso; apply lm1 with (a := a) (p := p); assumption.
  - exfalso; apply lm1 with (a := a) (p := p); assumption.
  - hauto.
  - hauto.
  - destruct a; ssimpl;
    rewrite trv;
    apply Common.lu2;
    apply IHp. reflexivity.
    assumption.
  - destruct a; ssimpl;
    rewrite trv;
    apply Common.lu2;
    apply IHp. reflexivity.
    assumption.
  - destruct a; ssimpl;
    rewrite trv;
    apply Common.lu2;
    apply IHp. reflexivity.
    assumption.
  - destruct a; ssimpl;
    rewrite trv;
    apply Common.lu2;
    apply IHp. reflexivity.
    assumption.
  - destruct a; ssimpl;
    rewrite trv;
    apply Common.lu2;
    apply IHp.
  - destruct a; ssimpl;
    rewrite trv; apply Common.lu2; apply Common.lu2;
    apply IHp; try reflexivity; try assumption.
  - destruct a; ssimpl;
    rewrite trv;
    apply Common.lu2;
    apply IHp. reflexivity. assumption.
  - destruct a; ssimpl;
    rewrite trv;
    apply Common.lu2;
    apply IHp.
  - destruct a; ssimpl;
    rewrite trv;
    apply Common.lu2;
    apply IHp.
Qed.

Lemma comp_instr : forall prog pc i,
                   Common.lookup prog pc i ->
                   Common.lookup (Compiler.compile'' prog) 
                                 (Compiler.compile_index prog pc)
                                 (Compiler.comp_first i).
Proof.
  assert (forall p q pc i,
                      Compiler.compile'' p = q ->
                      Common.lookup p pc i ->
                      Common.lookup q (Compiler.compile_index p pc)
                                      (Compiler.comp_first i)).
  apply comp_instr_lm.
  auto.
Qed.


Lemma link_stable : 
  forall p ind i,
  (forall n, i <> Assembly.UJUMP /\ i <> Assembly.URET /\ i <> Assembly.Jump n) ->
  Common.lookup p ind i -> 
  Common.lookup (Compiler.link p) ind i.
Proof.
Admitted.

Lemma lm2 : forall p, Compiler.compile_index p 0 = 0.
Proof.
Admitted.

Lemma lm3 : forall p i ins,
                        (ins <> Language.Jump /\ ins <> Language.Ret) ->
                        Common.lookup p i ins ->
                        Compiler.compile_index p i + 1 =
                        Compiler.compile_index p (i + 1).
Admitted.

Theorem th : Simulation.plus_forward_sim Compiler.compile 
             Language.semantics Assembly.semantics.
Proof.
  unfold Simulation.plus_forward_sim.
  intros.
  inversion H.
  assert (forall q2, Assembly.semantics q q2 -> Assembly.prog q2 = Assembly.prog q).
  sauto.
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
      apply link_stable. auto with *.
      rewrite H.
      apply comp_instr.
      assumption.
    + simpl.
      unfold Language.read_instr in r.
      inversion r.
      * destruct p'; ssimpl.
        destruct p; ssimpl.
        assert (Compiler.compile_index xs 0 = 0).
        apply lm2.
        rewrite H.
        reflexivity.
      * rewrite H;
        rewrite <- e;
        rewrite <- e0;
        rewrite H0;
        destruct p; ssimpl; f_equal; rewrite trv; rewrite trv; f_equal;
        (apply lm3 with (ins := Language.PtrInc)); try (split; discriminate);
        assumption.
    + simpl; reflexivity.
    + simpl; assumption.
    + simpl; inversion e1; reflexivity.
Admitted.

End Verification.