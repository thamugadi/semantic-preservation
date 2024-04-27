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
  induction p; destruct q; destruct i; intros; try inversion H; inversion H0;
  (assert (Compiler.compile'' (a :: p) = [] -> False) by apply lm1); 
  try (exfalso; apply H6; assumption); ssimpl;
  try (repeat apply Common.lu2; rewrite trv; now apply IHp).
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
  (forall n, i <> Assembly.Jump n /\ i <> Assembly.UJUMP /\ i <> Assembly.URET) ->
  Common.lookup p ind i -> 
  Common.lookup (Compiler.link p) ind i.
Proof.
  intros.
  rewrite Compiler.link_eq.
  induction H0.
  - ssimpl.
    + exfalso. apply H1. exact 0. reflexivity.
    + exfalso. apply H0. exact 0. reflexivity.
  - assert (Common.lookup (Compiler.link_aux xs) i y).
    apply IHlookup.
    sfirstorder.
    apply Compiler.lookup_link_stable.
    apply H.
    assumption.
Qed.

Lemma lm2 : forall p, Compiler.compile_index p 0 = 0.
Proof.
  destruct p;
  now reflexivity.
Qed.

Lemma lm3 : forall p i ins,
                        (ins <> Language.Jump /\ ins <> Language.Ret) ->
                        Common.lookup p i ins ->
                        Compiler.compile_index p i + 1 =
                        Compiler.compile_index p (i + 1).
Proof.
  intros; destruct ins; ssimpl;
  induction H0; ssimpl; f_equal;
  assert (forall p, Compiler.compile_index p 0 = 0) by apply lm2; ssimpl;
  rewrite trv; rewrite trv; repeat f_equal; try assumption.
Qed.

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
  - apply Common.t_base.
    apply Assembly.sub with (imm := 1).
    + unfold Language.read_instr, Assembly.read_instr in *.
      qsimpl.
      assert (Assembly.Sub 1 = Compiler.comp_first Language.PtrDec).
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
        (apply lm3 with (ins := Language.PtrDec)); try (split; discriminate);
        assumption.
    + simpl; reflexivity.
    + simpl; assumption.
    + simpl; inversion e1; reflexivity.
  - apply Common.t_base.
    apply Assembly.add_ptr with (imm := 1).
    + unfold Language.read_instr, Assembly.read_instr in *.
      assert (Assembly.AddPtr 1 = Compiler.comp_first Language.Inc).
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
      * rewrite H. 
        rewrite <- e.
        rewrite <- e0.
        rewrite H1; destruct p; ssimpl; f_equal; rewrite trv; rewrite trv; f_equal;
        (apply lm3 with (ins := Language.Inc)); try (split; discriminate);
        assumption.
    + now reflexivity.
    + simpl.
      destruct p, p'; ssimpl.
    + ssimpl.
    + rewrite <- e1 in *. ssimpl.
  - apply Common.t_base.
    apply Assembly.sub_ptr with (imm := 1).
    + unfold Language.read_instr, Assembly.read_instr in *.
      assert (Assembly.SubPtr 1 = Compiler.comp_first Language.Dec).
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
      * rewrite H. 
        rewrite <- e.
        rewrite <- e0.
        rewrite H1; destruct p; ssimpl; f_equal; rewrite trv; rewrite trv; f_equal;
        (apply lm3 with (ins := Language.Dec)); try (split; discriminate);
        assumption.
    + now reflexivity.
    + simpl.
      destruct p, p'; ssimpl.
    + ssimpl.
    + rewrite <- e1 in *. ssimpl.
  - destruct p'; ssimpl.
  - remember (
    {| Assembly.prog := Compiler.link (Compiler.compile'' (Language.prog p));
       Assembly.mem := Language.mem p';
       Assembly.pc := Compiler.compile_index (Language.prog p')
                      (Language.pc p');
       Assembly.ac := Language.ptr p' |}) as q'.
    assert (Assembly.read_instr (Compiler.compile' p) Assembly.Skip) as H1.
    unfold Language.read_instr in r.
    unfold Assembly.read_instr.
    unfold Compiler.compile'. ssimpl.
    apply link_stable. auto with *.
    assert (Assembly.Skip = Compiler.comp_first Language.Jump).
    auto.
    rewrite H.
    apply comp_instr; assumption.
    (* skip not taken: q_inter points to Assembly.Jump n *)
    pose (q_inter :=
    {| Assembly.prog := Assembly.prog (Compiler.compile' p);
       Assembly.mem := Assembly.mem (Compiler.compile' p);
       Assembly.pc := Assembly.pc (Compiler.compile' p) + 1;
       Assembly.ac := Assembly.ac (Compiler.compile' p);|}).
    assert (Assembly.semantics (Compiler.compile' p) q_inter).
    apply Assembly.skipz; auto.
    (*remove exists*)
    + assert (exists n, Assembly.read_instr q_inter (Assembly.Jump n)).
      admit.
      apply Common.t_trans with (y := q_inter).
      admit.
      apply Common.t_base.
      destruct H2.
      rename x into n.
      apply Assembly.jump with (addr := n).
      * admit.
      * admit.
      * admit.
      * admit.
      * admit.
  - destruct p'; ssimpl.
  - admit.
  - destruct p'; ssimpl.
  - admit.
  - destruct p'; ssimpl.
  - admit.
Admitted.

End Verification.