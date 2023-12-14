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

Require Import Coq.Program.Equality.

From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
From Hammer Require Import Reflect.

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

(* unnecessary
Theorem first_instr_comp' : 
  forall p q i x, Compiler.compile p q ->
  Language.read_instr' p.(Language.prog) x = i ->
  Assembly.read_instr' q.(Assembly.prog) (Compiler.new_pc p.(Language.prog) x)
  = (first_comp_instr i).
Proof.
Admitted.
*)


(* A minimal version is available in prototype/Example.v *)
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
Compute (Compiler.new_pc [Language.PtrInc] 1 ).

Theorem offset_newpc_lm :
  forall p p',
  eval p p' -> Compiler.new_pc (Language.prog p') (Language.pc p') =
               Compiler.new_pc (Language.prog p) (Language.pc p) 
               + length (Compiler.compile'' [Language.read_instr' (Language.prog p) (Language.pc p)]).
Admitted.

Theorem offset_newpc :
  forall p p',
  eval p p' -> Compiler.new_pc (Language.prog p') (Language.pc p') =
               Compiler.new_pc (Language.prog p) (Language.pc p) 
               + emitted_instr (Language.read_instr' p.(Language.prog) p.(Language.pc)).
Proof.
  intros.
  assert (Compiler.new_pc (Language.prog p') (Language.pc p') =
               Compiler.new_pc (Language.prog p) (Language.pc p) 
               + length (Compiler.compile'' [Language.read_instr' (Language.prog p) (Language.pc p)])).
  apply offset_newpc_lm. assumption.
  destruct (length
       (Compiler.compile''
          [Language.read_instr' (Language.prog p)
             (Language.pc p)])) eqn:HA.
  ssimpl.
  ssimpl.
Qed.
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

Theorem inc_instr_comp :
  forall p q p', Compiler.compile p q -> eval p p' ->
              Language.read_instr p Language.Inc ->
              exists q1 q2 q3 q4 q5,
              (Assembly.read_instr q1 Assembly.Load /\
              Assembly.read_instr q2 (Assembly.Add 1) /\
              Assembly.read_instr q3 Assembly.Store /\
              Assembly.read_instr q4 Assembly.Zero /\
              Assembly.read_instr q5 Assembly.Swap /\
              eval' q q1 /\ eval' q1 q2 /\ eval' q2 q3 /\ eval' q3 q4 /\ eval' q4 q5).
Proof.
  intros.
  assert (Assembly.read_instr q (first_comp_instr Language.Inc)).
  apply first_instr_comp with (p := p). assumption. assumption.
  simpl in H2.
Admitted.

Theorem dec_instr_comp :
  forall p q p', Compiler.compile p q -> eval p p' ->
              Language.read_instr p Language.Dec ->
              exists q1 q2 q3 q4 q5,
              (Assembly.read_instr q1 Assembly.Load /\
              Assembly.read_instr q2 (Assembly.Sub 1) /\
              Assembly.read_instr q3 Assembly.Store /\
              Assembly.read_instr q4 Assembly.Zero /\
              Assembly.read_instr q5 Assembly.Swap /\
              eval' q q1 /\ eval' q1 q2 /\ eval' q2 q3 /\ eval' q3 q4 /\ eval' q4 q5).
Proof.
  intros.
  assert (Assembly.read_instr q (first_comp_instr Language.Dec)).
  apply first_instr_comp with (p := p). assumption. assumption.
  simpl in H2.
Admitted.

Theorem jump_instr_comp :
  forall p q p', Compiler.compile p q -> eval p p' -> 
                 Language.read_instr p Language.Jump ->
                 (exists n q1, Assembly.read_instr q1 (Assembly.Jump n) /\ eval' q q1).
Proof.
  intros.
  assert (Assembly.read_instr q (first_comp_instr Language.Jump)).
  apply first_instr_comp with (p := p). assumption. assumption.
  simpl in H2.
Admitted.

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

Compute (Assembly.mkState [Assembly.Halt] [1] 4 4 4).

Theorem sequence_comp_inc :
  forall p p' q q', Compiler.compile p q -> eval p p' -> Compiler.compile p' q' ->
              Language.read_instr p Language.Inc ->
              Common.plus eval' q q'.
Proof.
  intros.
  assert (Assembly.read_instr q (Assembly.Swap)).
  apply (comp_newstate' p q Language.Inc); assumption.
  assert (exists q1 q2 q3 q4 q5,
              Assembly.read_instr q1 Assembly.Load /\
              Assembly.read_instr q2 (Assembly.Add 1) /\
              Assembly.read_instr q3 Assembly.Store /\
              Assembly.read_instr q4 Assembly.Zero /\
              Assembly.read_instr q5 Assembly.Swap /\
              eval' q q1 /\ eval' q1 q2 /\ eval' q2 q3 /\ eval' q3 q4 /\ eval' q4 q5).
  apply inc_instr_comp with (p := p) (p' := p'); assumption.
  
  destruct H4. destruct H4. destruct H4. destruct H4. destruct H4.
  rename x into q1; rename x0 into q2; rename x1 into q3; rename x2 into q4; rename x3 into q5.
  destruct H4.
  destruct H5.
  destruct H6.
  destruct H7.
  destruct H8.
  destruct H9.
  destruct H10.
  destruct H11.
  destruct H12.
  apply (Common.t_trans) with (y := q1).
  assumption.
  apply (Common.t_trans) with (y := q2).
  assumption.
  apply (Common.t_trans) with (y := q3).
  assumption.
  apply (Common.t_trans) with (y := q4).
  assumption.
  apply (Common.t_trans) with (y := q5).
  assumption.
  apply (Common.t_base).
  apply Assembly.swap; admit.
Admitted.
Theorem sequence_comp_dec :
  forall p p' q q', Compiler.compile p q -> eval p p' -> Compiler.compile p' q' ->
              Language.read_instr p Language.Dec ->
              Common.plus eval' q q'.
Proof.
  intros.
  assert (Assembly.read_instr q (Assembly.Swap)).
  apply (comp_newstate' p q Language.Dec); assumption.
  assert (exists q1 q2 q3 q4 q5,
              Assembly.read_instr q1 Assembly.Load /\
              Assembly.read_instr q2 (Assembly.Sub 1) /\
              Assembly.read_instr q3 Assembly.Store /\
              Assembly.read_instr q4 Assembly.Zero /\
              Assembly.read_instr q5 Assembly.Swap /\
              eval' q q1 /\ eval' q1 q2 /\ eval' q2 q3 /\ eval' q3 q4 /\ eval' q4 q5).
  apply dec_instr_comp with (p := p) (p' := p'); assumption.
  
  destruct H4. destruct H4. destruct H4. destruct H4. destruct H4.
  rename x into q1; rename x0 into q2; rename x1 into q3; rename x2 into q4; rename x3 into q5.
  destruct H4.
  destruct H5.
  destruct H6.
  destruct H7.
  destruct H8.
  destruct H9.
  destruct H10.
  destruct H11.
  destruct H12.
  apply (Common.t_trans) with (y := q1).
  assumption.
  apply (Common.t_trans) with (y := q2).
  assumption.
  apply (Common.t_trans) with (y := q3).
  assumption.
  apply (Common.t_trans) with (y := q4).
  assumption.
  apply (Common.t_trans) with (y := q5).
  assumption.
  apply (Common.t_base).
  apply Assembly.swap; admit.
Admitted.
Theorem sequence_comp_jump :
  forall p p' q q', Compiler.compile p q -> eval p p' -> Compiler.compile p' q' -> Language.read_instr p Language.Jump -> Common.plus eval' q q'.
Proof.
  intros.
  assert (Assembly.read_instr q (Assembly.Skip)).
  apply (comp_newstate' p q Language.Jump); assumption.
  assert (exists n q1, Assembly.read_instr q1 (Assembly.Jump n) /\ eval' q q1).
  apply jump_instr_comp with (p := p) (p' := p'); assumption.
  
  destruct H4.
  destruct H4.
  destruct H4.
  rename x into n. rename x0 into q1.

  apply (Common.t_trans) with (y := q1).
  assumption.
  apply (Common.t_base).
  apply Assembly.jump with (n := n); admit.
Admitted.

(* the main theorem: *)

Theorem comp_correct : Simulation.plus_forward_sim Compiler.compile eval eval'.
Proof.
  unfold Simulation.plus_forward_sim.
  intros p q compileH p' evalH.
  assert (Compiler.matched (Language.prog p')). ssimpl.
  inversion evalH; exists (Compiler.compile' p'); (split; try (apply Compiler.comp_r); auto).
  + apply sequence_comp_ptrinc with (p := p) (p' := p').
    assumption. assumption. apply Compiler.comp_r. assumption. reflexivity. assumption.
  + apply sequence_comp_ptrdec with (p := p) (p' := p').
    assumption. assumption. apply Compiler.comp_r. assumption. reflexivity. assumption. 
  + apply sequence_comp_inc with (p := p) (p' := p').
    assumption. assumption. apply Compiler.comp_r. assumption. reflexivity. assumption. 
  + apply sequence_comp_dec with (p := p) (p' := p').
    assumption. assumption. apply Compiler.comp_r. assumption. reflexivity. assumption. 
  + apply sequence_comp_jump with (p := p) (p' := p').
    assumption. assumption. apply Compiler.comp_r. assumption. reflexivity. assumption.
  + apply sequence_comp_jump with (p := p) (p' := p').
    assumption. assumption. apply Compiler.comp_r. assumption. reflexivity. assumption.
  + apply sequence_comp_jump with (p := p) (p' := p').
    assumption. assumption. apply Compiler.comp_r. assumption. reflexivity. assumption.
  + apply sequence_comp_jump with (p := p) (p' := p').
    assumption. assumption. apply Compiler.comp_r. assumption. reflexivity. assumption.
Qed.

End Verification.