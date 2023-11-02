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

Theorem constant_code : forall p p', eval p p' -> p.(Language.prog) = p'.(Language.prog).
Proof.
  intros.
  inversion H; assumption.
Qed.
Theorem constant_asm' : forall q q', eval' q q' -> q.(Assembly.prog) = q'.(Assembly.prog).
Proof.
  intros.
  inversion H; assumption.
Qed.
Theorem constant_asm : forall p p' q q', Compiler.compile p q -> Compiler.compile p' q' ->
                       eval p p' -> q.(Assembly.prog) = q'.(Assembly.prog).
Proof.
  intros.
  inversion H.
  inversion H0.
  unfold Compiler.compile' in H3, H5.
  rewrite H3.
  rewrite H5.
  simpl.
  assert (Language.prog p = Language.prog p').
  apply constant_code.
  assumption.
  rewrite H6.
  reflexivity.
Qed.

Theorem match_preserve : 
  forall p p', Language.semantics p p' ->
               Compiler.matched (Language.prog p) ->
               Compiler.matched (Language.prog p').
Proof.
  intros.
  assert (p.(Language.prog) = p'.(Language.prog)).
  - apply constant_code.
    assumption.
  - destruct p, p'.
    simpl in H1.
    simpl.
    simpl in H0.
    rewrite H1 in H0.
    assumption.
Qed.
  
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

Theorem first_instr_comp' : 
  forall p q i x, Compiler.compile p q ->
  Language.read_instr' p.(Language.prog) x = i ->
  Assembly.read_instr' q.(Assembly.prog) (Compiler.new_pc p.(Language.prog) x)
  = (first_comp_instr i).
Proof.
Admitted.
Theorem first_instr_comp : forall p q i, Compiler.compile p q ->
                           Language.read_instr p i ->
                           Assembly.read_instr q (first_comp_instr i).
Proof.
  intros.
  inversion H.
  inversion H0.
  apply Assembly.ri.
  rewrite H2.
  rewrite <- H3.
  generalize (Language.pc p) as x.
  induction p; intro x; destruct x; unfold first_comp_instr.
Admitted.
Theorem inc_instr_comp :
  forall p q, Compiler.compile p q -> Language.read_instr p Language.Inc ->
              exists q1 q2 q3 q4 q5,
              Assembly.read_instr q5 Assembly.Swap /\
              eval' q q1 /\ eval' q1 q2 /\ eval' q2 q3 /\ eval' q3 q4 /\ eval' q4 q5.
Proof.
Admitted.

Theorem dec_instr_comp :
  forall p q, Compiler.compile p q -> Language.read_instr p Language.Dec ->
              exists q1 q2 q3 q4 q5,
              Assembly.read_instr q5 Assembly.Swap /\
              eval' q q1 /\ eval' q1 q2 /\ eval' q2 q3 /\ eval' q3 q4 /\ eval' q4 q5.
Proof.
Admitted.

Theorem jump_instr_comp :
  forall p q, Compiler.compile p q -> Language.read_instr p Language.Jump ->
              exists n q1, Assembly.read_instr q1 (Assembly.Jump n) /\ eval' q q1.
Proof.
Admitted.
Theorem ret_instr_comp :
  forall p q, Compiler.compile p q -> Language.read_instr p Language.Ret ->
              exists n q1, Assembly.read_instr q1 (Assembly.Jump n) /\ eval' q q1.
Proof.
Admitted.

Theorem comp_newstate :
  forall p q, Compiler.compile p q ->
              q.(Assembly.pc) = Compiler.new_pc (p.(Language.prog)) (p.(Language.pc)) /\
              q.(Assembly.ac) = p.(Language.ptr) /\
              q.(Assembly.mem) = p.(Language.mem) /\
              q.(Assembly.b) = 0 /\
              Assembly.read_instr q (first_comp_instr
              (Language.read_instr' p.(Language.prog) p.(Language.pc))).
Proof.
  intros.
  inversion H.
  inversion H1.
  unfold Compiler.compile'.
  simpl.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  apply first_instr_comp with (p := p).
  destruct q.
  inversion H2.
  apply Compiler.comp_r.
  assumption.
  unfold Compiler.compile'.
  reflexivity.
  apply Language.ri.
  reflexivity.
Qed.
Theorem comp_newstate' :
  forall p q i, Compiler.compile p q -> Language.read_instr p i ->
              q.(Assembly.pc) = Compiler.new_pc (p.(Language.prog)) (p.(Language.pc)) /\
              q.(Assembly.ac) = p.(Language.ptr) /\
              q.(Assembly.mem) = p.(Language.mem) /\
              q.(Assembly.b) = 0 /\
              Assembly.read_instr q (first_comp_instr i).
Proof.
  intros.
  inversion H.
  inversion H2.
  unfold Compiler.compile'.
  simpl.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  inversion H0.
  rewrite <- H4.
  apply comp_newstate.
  apply Compiler.comp_r.
  assumption.
  unfold Compiler.compile'.
  reflexivity.
Qed.
Definition emitted_instr (i : Language.instr) : nat :=
  match i with
  | Language.PtrInc => 1
  | Language.PtrDec => 1
  | Language.Inc => 6
  | Language.Dec => 6
  | Language.Jump => 2
  | Language.Ret => 2
  | Language.Halt => 1
  end.

Theorem offset_newpc :
  forall p p',
  eval p p' -> Compiler.new_pc (Language.prog p') (Language.pc p') =
               Compiler.new_pc (Language.prog p) (Language.pc p) 
               + emitted_instr (Language.read_instr' p.(Language.prog) p.(Language.pc)).
Proof.
Admitted. (*to be done*)

Lemma read_instr_functional : forall p i j,
  Language.read_instr p i -> Language.read_instr p j -> i <> j -> False.
Proof.
  intros.
  inversion H0.
  inversion H.
  assert ((Language.read_instr' (Language.prog p) (Language.pc p) = 
             Language.read_instr' (Language.prog p) (Language.pc p))).
  reflexivity.
  rewrite <- H2 in H1.
  rewrite <- H3 in H1.
  contradiction.
Qed.

Theorem sequence_comp_ptrinc :
  forall p p' q q', Compiler.compile p q -> eval p p' -> Compiler.compile p' q' ->
              Language.read_instr p Language.PtrInc ->
              Common.plus eval' q q'.
Proof.
  intros.
  apply Common.t_base.
  assert (Assembly.read_instr q (Assembly.Add 1)).
  apply (comp_newstate' p q Language.PtrInc).
  assumption.
  assumption.
  assert (Assembly.read_instr q' (first_comp_instr
                                 (Language.read_instr' p'.(Language.prog) p'.(Language.pc)))).
  apply (comp_newstate' p' q').
  assumption.
  apply Language.ri.
  reflexivity.
  unfold eval'.
  apply (Assembly.add q) with (n := 1).
  - assumption.
  - assert (Assembly.pc q = (Compiler.new_pc p.(Language.prog) p.(Language.pc))).
    inversion H.
    inversion H6.
    unfold Compiler.compile'.
    simpl.
    reflexivity.
    assert (Assembly.pc q' = (Compiler.new_pc p'.(Language.prog) p'.(Language.pc))).
    inversion H1.
    unfold Compiler.compile' in H7.
    inversion H1.
    inversion H9.
    unfold Compiler.compile'.
    simpl.
    reflexivity.
    assert (Compiler.new_pc (Language.prog p') (Language.pc p') =
            Compiler.new_pc (Language.prog p) (Language.pc p) + emitted_instr (Language.read_instr' p.(Language.prog) p.(Language.pc))).
    inversion H2.
    assert (emitted_instr (Language.read_instr' p.(Language.prog) p.(Language.pc)) = 1).
    rewrite H7.
    simpl.
    reflexivity.
    apply offset_newpc.
    assumption.
    rewrite H7 in H6.
    inversion H2.
    rewrite H8 in H6.
    simpl in H6.
    rewrite <- H5 in H6.
    rewrite H6.
    reflexivity.
  - inversion H.
    inversion H6.
    unfold Compiler.compile'.
    inversion H1.
    inversion H9.
    unfold Compiler.compile'.
    simpl.
    f_equal.
    f_equal.
    apply constant_code.
    assumption.
  - inversion H.
    inversion H6.
    unfold Compiler.compile'.
    simpl.
    assert (Language.mem p' = Language.mem p).
    inversion H0.
    rewrite H12. reflexivity.
    exfalso.
    apply (read_instr_functional _ _ _ H8 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H8 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H8 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H8 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H8 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H8 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H8 H2).
    discriminate.
    rewrite <- H8.
    inversion H1.
    inversion H10.
    unfold Compiler.compile'.
    simpl.
    reflexivity.
  - assert (Assembly.b q = 0).
    inversion H.
    inversion H6.
    unfold Compiler.compile'.
    simpl.
    reflexivity.
    assert (Assembly.b q' = 0).
    inversion H1.
    inversion H7.
    unfold Compiler.compile'.
    simpl.
    reflexivity.
    rewrite H5, H6.
    reflexivity.
  - inversion H.
    inversion H6.
    unfold Compiler.compile'.
    simpl.
    inversion H1.
    inversion H9.
    unfold Compiler.compile'.
    simpl.
    inversion H0.
    rewrite H12.
    reflexivity.
    exfalso.
    apply (read_instr_functional _ _ _ H11 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H11 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H11 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H11 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H11 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H11 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H11 H2).
    discriminate.
Qed.
Theorem sequence_comp_ptrdec :
  forall p p' q q', Compiler.compile p q -> eval p p' -> Compiler.compile p' q' ->
              Language.read_instr p Language.PtrDec ->
              Common.plus eval' q q'.
Proof.
  intros.
  apply Common.t_base.
  assert (Assembly.read_instr q (Assembly.Sub 1)).
  apply (comp_newstate' p q Language.PtrDec).
  assumption.
  assumption.
  assert (Assembly.read_instr q' (first_comp_instr
                                 (Language.read_instr' p'.(Language.prog) p'.(Language.pc)))).
  apply (comp_newstate' p' q').
  assumption.
  apply Language.ri.
  reflexivity.
  unfold eval'.
  apply (Assembly.sub q) with (n := 1).
  - assumption.
  - assert (Assembly.pc q = (Compiler.new_pc p.(Language.prog) p.(Language.pc))).
    inversion H.
    inversion H6.
    unfold Compiler.compile'.
    simpl.
    reflexivity.
    assert (Assembly.pc q' = (Compiler.new_pc p'.(Language.prog) p'.(Language.pc))).
    inversion H1.
    unfold Compiler.compile' in H7.
    inversion H1.
    inversion H9.
    unfold Compiler.compile'.
    simpl.
    reflexivity.
    assert (Compiler.new_pc (Language.prog p') (Language.pc p') =
            Compiler.new_pc (Language.prog p) (Language.pc p) + emitted_instr (Language.read_instr' p.(Language.prog) p.(Language.pc))).
    inversion H2.
    assert (emitted_instr (Language.read_instr' p.(Language.prog) p.(Language.pc)) = 1).
    rewrite H7.
    simpl.
    reflexivity.
    apply offset_newpc.
    assumption.
    rewrite H7 in H6.
    inversion H2.
    rewrite H8 in H6.
    simpl in H6.
    rewrite <- H5 in H6.
    rewrite H6.
    reflexivity.
  - inversion H.
    inversion H6.
    unfold Compiler.compile'.
    inversion H1.
    inversion H9.
    unfold Compiler.compile'.
    simpl.
    f_equal.
    f_equal.
    apply constant_code.
    assumption.
  - inversion H.
    inversion H6.
    unfold Compiler.compile'.
    simpl.
    assert (Language.mem p' = Language.mem p).
    inversion H0.
    exfalso.
    apply (read_instr_functional _ _ _ H8 H2).
    discriminate.
    rewrite H12.
    reflexivity.
    exfalso.
    apply (read_instr_functional _ _ _ H8 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H8 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H8 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H8 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H8 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H8 H2).
    discriminate.
    rewrite <- H8.
    inversion H1.
    inversion H10.
    unfold Compiler.compile'.
    simpl.
    reflexivity.
  - assert (Assembly.b q = 0).
    inversion H.
    inversion H6.
    unfold Compiler.compile'.
    simpl.
    reflexivity.
    assert (Assembly.b q' = 0).
    inversion H1.
    inversion H7.
    unfold Compiler.compile'.
    simpl.
    reflexivity.
    rewrite H5, H6.
    reflexivity.
  - inversion H.
    inversion H6.
    unfold Compiler.compile'.
    simpl.
    inversion H1.
    inversion H9.
    unfold Compiler.compile'.
    simpl.
    inversion H0.
    exfalso.
    apply (read_instr_functional _ _ _ H11 H2).
    discriminate.
    rewrite H12.
    reflexivity.
    exfalso.
    apply (read_instr_functional _ _ _ H11 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H11 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H11 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H11 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H11 H2).
    discriminate.
    exfalso.
    apply (read_instr_functional _ _ _ H11 H2).
    discriminate.
Qed.
Theorem sequence_comp_inc :
  forall p p' q q', Compiler.compile p q -> eval p p' -> Compiler.compile p' q' ->
              Language.read_instr p Language.Inc ->
              Common.plus eval' q q'.
Proof.
  intros.
  assert (exists q1 q2 q3 q4 q5,
              Assembly.read_instr q5 Assembly.Swap /\
              eval' q q1 /\ eval' q1 q2 /\ eval' q2 q3 /\ eval' q3 q4 /\ eval' q4 q5).
  apply inc_instr_comp with (p := p).
  assumption.
  assumption.
  destruct H3 as [q1]. destruct H3 as [q2]. destruct H3 as [q3].
  destruct H3 as [q4]. destruct H3 as [q5].
  destruct H3. destruct H4. destruct H5.
  destruct H6. destruct H7.
  apply Common.t_trans with (y := q1). assumption.
  apply Common.t_trans with (y := q2). assumption.
  apply Common.t_trans with (y := q3). assumption.
  apply Common.t_trans with (y := q4). assumption.
  apply Common.t_trans with (y := q5). assumption.
  apply Common.t_base.
  assert (Assembly.read_instr q' (first_comp_instr
                                 (Language.read_instr' p'.(Language.prog) p'.(Language.pc)))).
  apply (comp_newstate' p' q').
  assumption.
  apply Language.ri.
  reflexivity.
  unfold eval'.
  apply (Assembly.swap).
  assumption.
  - assert (Assembly.prog q = Assembly.prog q').
    apply constant_asm with (p := p) (p' := p').
    assumption.
    assumption.
    assumption.
    rewrite <- H10.
    assert (Assembly.prog q4 = Assembly.prog q5) by (apply constant_asm'; assumption).
    assert (Assembly.prog q3 = Assembly.prog q4) by (apply constant_asm'; assumption).
    assert (Assembly.prog q2 = Assembly.prog q3) by (apply constant_asm'; assumption).
    assert (Assembly.prog q1 = Assembly.prog q2)  by (apply constant_asm'; assumption).
    assert (Assembly.prog q = Assembly.prog q1) by (apply constant_asm'; assumption).
    rewrite H15. rewrite H14. rewrite H13. rewrite H12. rewrite H11.
    reflexivity.
  - inversion H1.
    unfold Compiler.compile' in H11.
    inversion H8.
    (* unfinished. *)
Admitted.
Theorem sequence_comp_dec :
  forall p p' q q', Compiler.compile p q -> eval p p' -> Compiler.compile p' q' ->
              Language.read_instr p Language.Dec ->
              Common.plus eval' q q'.
Proof.
Admitted.
Theorem sequence_comp_jump :
  forall p p' q q', Compiler.compile p q -> eval p p' -> Compiler.compile p' q' ->
              Language.read_instr p Language.Jump ->
              Common.plus eval' q q'.
Proof.
Admitted.
Theorem sequence_comp_ret :
  forall p p' q q', Compiler.compile p q -> eval p p' -> Compiler.compile p' q' ->
              Language.read_instr p Language.Ret ->
              Common.plus eval' q q'.
Proof.
Admitted.

(* the main theorem: *)
Theorem comp_correct : Simulation.plus_forward_sim Compiler.compile eval eval'.
Proof.
  unfold Simulation.plus_forward_sim.
  intros p q compileH p' evalH.
  assert (Compiler.matched (Language.prog p')).
  apply match_preserve with (p := p).
  assumption.
  inversion compileH.
  assumption.
  inversion evalH.
  - exists (Compiler.compile' p').
    split.
    + apply Compiler.comp_r.
      assumption.
      reflexivity.
    + inversion compileH.
      remember (Compiler.compile' p') as q'.
      apply sequence_comp_ptrinc with (p := p) (p' := p').
      assumption.
      assumption.
      apply Compiler.comp_r.
      assumption.
      assumption.
      assumption.
(* etc. *)
Admitted.

End Verification.