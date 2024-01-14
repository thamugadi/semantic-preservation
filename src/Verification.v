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
Lemma comp_len_eq : forall n m p p', eval p p' ->
                    @Compiler.comp_len n (@Language.prog n m p) =
                    @Compiler.comp_len n (@Language.prog n m p').
Proof.
  intros.
  assert (p.(Language.prog) = p'.(Language.prog)).
  + inversion H; assumption.
  + inversion H0.
    reflexivity.
Defined.

Definition comp_len_f
 {n n' m p p'} (H : eval p p') 
 (q : @Assembly.state (@Compiler.comp_len n (@Language.prog n m p')) n') 
 : @Assembly.state (@Compiler.comp_len n (@Language.prog n m p)) n'.
Proof.
  assert (@Compiler.comp_len n (@Language.prog n m p) =
          @Compiler.comp_len n (@Language.prog n m p')).
  - apply comp_len_eq.
    assumption.
  - rewrite H0.
    exact q.
Defined.
  
Lemma match_tr {n m} : forall p p', Compiler.matched (n := n) (Language.prog p) ->
                       eval p p' -> Compiler.matched (Language.prog p' (m := m)).
Proof.
  intros.
  assert (Language.prog p = Language.prog p').
  - inversion H0; assumption.
  - rewrite <- H1.
    assumption.
Qed.

Lemma comp_link_prog {n m} : forall p HA HA1 q, Compiler.compile_link p HA HA1 = q ->
                             q.(Assembly.prog) =
                             Compiler.link (@Compiler.compile'' n p.(@Language.prog n m)).
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

Definition len_asm (i : Assembly.instr) : nat :=
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

Definition vec_len {A n} (v : Vector.t A n) : nat := n.

Lemma read_instr_eq {n} : forall p i,
                          (Compiler.compile'' p)[@@Compiler.compile_index n p i]
                          = @Compiler.compile_first n p[@i].
Proof.
  induction i; dependent destruction p;
  destruct h; simpl;
  try (now reflexivity);
  try (apply IHi).
Qed.

(*todo: prove another lemma generalizing this one for N compiled instructions*)
(*todo: find a lemma as general as read_instr_eq for link*)

Lemma link_stable : forall n p ind i, (i <> Assembly.UJUMP /\ i <> Assembly.URET) ->
                    p[@ind] = i -> (@Compiler.link n p)[@ind] = i.
Admitted.
  
Lemma read_comp_ptrinc {n m} : forall p H1 H2, Language.read_instr p Language.PtrInc ->
                               Assembly.read_instr
                              (@Compiler.compile_link n m p H1 H2) (Assembly.Add 1).
Proof.
  unfold Compiler.compile_link.
  unfold Compiler.compile'.
  intros.
  ssimpl.
  unfold Language.read_instr' in H0.
  apply Assembly.ri.
  unfold Assembly.read_instr'. simpl.
  assert ((Compiler.compile'' prog)[@Compiler.compile_index prog pc] =
  @Compiler.compile_first n prog[@pc]).
  apply read_instr_eq.
  rewrite H0 in H.
  simpl in H.
  apply link_stable.
  split; discriminate.
  assumption.
Qed.
  
  
Lemma read_comp_ptrdec {n m} : forall p H1 H2, Language.read_instr p Language.PtrDec ->
                               Assembly.read_instr (@Compiler.compile_link n m p H1 H2)
                               (Assembly.Sub 1).
Proof.
  unfold Compiler.compile_link.
  unfold Compiler.compile'.
  intros.
  ssimpl.
  unfold Language.read_instr' in H0.
  apply Assembly.ri.
  unfold Assembly.read_instr'. simpl.
  assert ((Compiler.compile'' prog)[@Compiler.compile_index prog pc] =
  @Compiler.compile_first n prog[@pc]).
  apply read_instr_eq.
  rewrite H0 in H.
  simpl in H.
  apply link_stable.
  split; discriminate.
  assumption.
Qed.

Lemma compiled_pc : forall n prog pc pc0 i, Language.read_instr' prog pc0 = i ->
                    Common.to_nat pc0 + 1 = Common.to_nat pc ->
                    Common.to_nat (Compiler.compile_index prog pc0) +
                    vec_len (Compiler.compile_one i 0)
                    = Common.to_nat (@Compiler.compile_index n prog pc).
Admitted.

Theorem comp_correct {n m : nat} :
    forall p q, Compiler.compile p q -> 
    forall p' (E : eval p p'), 
    exists q', Compiler.compile p' q' /\
    (Common.plus eval') q (comp_len_f (n := n) (n' := m) E q').
Proof.
  intros.
  assert (n <> 0).
  inversion H. assumption.
  assert (m <> 0).
  inversion H. assumption.
  exists (Compiler.compile_link p' H0 H1).
  split.
  - apply Compiler.comp_r with (H := H0) (H1 := H1).
    + assert (Compiler.matched (Language.prog p)).
      inversion H.
      assumption.
      apply match_tr with (p := p); assumption.
    + reflexivity. 
  - (unfold comp_len_f; unfold eq_rec_r; unfold eq_rec; unfold eq_rect).
    ssimpl.
    + apply Common.t_base.
      apply Assembly.add with (n' := 1).
      * assert (Assembly.read_instr (@Compiler.compile_link n m {|Language.prog := prog;
       Language.mem := mem;
       Language.pc := pc0;
       Language.ptr := ptr0|} H2 H3) (Assembly.Add 1)).
       apply read_comp_ptrinc. ssimpl.
       assumption.
      * simpl.
        unfold Common.to_nat.
        apply compiled_pc with (i := Language.PtrInc); assumption.
      * now reflexivity.
      * now reflexivity.
      * simpl. unfold Compiler.make_f1. ssimpl.
      * ssimpl.
    + apply Common.t_base.
      apply Assembly.sub with (n' := 1).
      * assert (Assembly.read_instr (@Compiler.compile_link n m {|Language.prog := prog;
       Language.mem := mem;
       Language.pc := pc0;
       Language.ptr := ptr0|} H2 H3) (Assembly.Sub 1)).
       apply read_comp_ptrdec. ssimpl.
       assumption.
      * simpl.
        apply compiled_pc with (i := Language.PtrDec); assumption.
      * now reflexivity.
      * now reflexivity.
      * simpl. unfold Compiler.make_f1. ssimpl.
      * ssimpl.
    + remember (Compiler.compile_link {|Language.prog := prog;Language.mem := mem0;
               Language.pc := pc0; Language.ptr := ptr|} H2 H3) as q.
      remember (Compiler.compile_link {|Language.prog := prog;Language.mem := mem;
               Language.pc := pc; Language.ptr := ptr|} H0 H1) as q'.
      assert (prog[@pc0] = Language.Inc). ssimpl.
      assert (Compiler.compile_one Language.Inc 0 =
             [Assembly.Swap; Assembly.Load; Assembly.Add 1;
             Assembly.Store;Assembly.Zero; Assembly.Swap]). 
      now reflexivity.
  
      assert (exists q1, eval' q q1).
      admit.
      destruct H6. remember x as q1.
      assert (exists q2, eval' q1 q2).
      admit.
      destruct H7. remember x0 as q2.
      assert (exists q3, eval' q2 q3).
      admit.
      destruct H8. remember x1 as q3.
      assert (exists q4, eval' q3 q4).
      admit.
      destruct H9. remember x2 as q4.
      assert (exists q5, eval' q4 q5).
      admit.
      destruct H10. remember x3 as q5.
      clear Heqq1 Heqq2 Heqq3 Heqq4 Heqq5 x x0 x1 x2 x3.
      apply Common.t_trans with (y := q1). assumption.
      apply Common.t_trans with (y := q2). assumption.
      apply Common.t_trans with (y := q3). assumption.
      apply Common.t_trans with (y := q4). assumption.
      apply Common.t_trans with (y := q5). assumption.
      apply Common.t_base. admit.
    + (*assert the existence of q1,q2,q3,q4,q5*) admit.

    (* will require other lemmas than read_comp: *)
    + (*assert the existence of q1*) admit.
    + (*assert the existence of q1*) admit.
    + (*assert the existence of q1*) admit.
    + (*assert the existence of q1*) admit.
Admitted.
End Verification.