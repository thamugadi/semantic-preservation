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

(* add similar lemmas with multiple read_instr *)

Lemma compiled_pc : forall n prog pc pc0 i, Language.read_instr' prog pc0 = i ->
                    Common.to_nat pc0 + 1 = Common.to_nat pc ->
                    Common.to_nat (Compiler.compile_index prog pc0) +
                    vec_len (Compiler.compile_one i 0)
                    = Common.to_nat (@Compiler.compile_index n prog pc).
Proof.
  intros.
  unfold Language.read_instr' in *.
  unfold vec_len.
  unfold Compiler.comp_len.
  simpl.
  induction pc.
  - exfalso.
    inversion H0.
    lia.
  - 
Admitted.

Compute (Compiler.compile_index [Language.Jump] Fin.F1).

Fixpoint weaken_fin_t {n : nat} (f : Fin.t n) : Fin.t (S n) :=
  match f in Fin.t n return Fin.t (S n) with
  | Fin.F1 => Fin.F1
  | Fin.FS f' => Fin.FS (weaken_fin_t f')
  end.

Definition safe_fs {n} (i : Fin.t n) (H : (Common.to_nat i) + 1 <> n) : Fin.t n.
Proof.
Admitted.

Lemma safe_fs_is_s {n} : forall i H,
                         @Common.to_nat n (safe_fs i H) = (Common.to_nat i) + 1.
Admitted. 


Lemma not_final_lm1 {n} : forall prog pc pc',
                          (@Common.to_nat n pc) + 1 = @Common.to_nat n pc' ->
                          Common.to_nat (Compiler.compile_index prog pc) + 1 <>
                          Compiler.comp_len prog.
Admitted.

Lemma not_final {n} : forall pc prog spc,
                     (Common.to_nat pc) + 1 = @Common.to_nat n spc ->
                     exists sqpc, @Common.to_nat (Compiler.comp_len prog) sqpc =
                     (Common.to_nat (@Compiler.compile_index n prog pc) + 1).
Proof.
  intros.
  assert (Common.to_nat (@Compiler.compile_index n prog pc) + 1 
          <> Compiler.comp_len prog).
  apply not_final_lm1 with (pc' := spc).
  assumption.
  exists (safe_fs (@Compiler.compile_index n prog pc) H0).
  apply safe_fs_is_s.
Qed.

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

      (*Here, we are going to prove the existence of intermediate states to which
        q evaluated to before getting to q' (which is compiled p') *)
      assert (exists q1, eval' q q1).
      assert (Assembly.read_instr 
             (@Compiler.compile_link n m {|Language.prog := prog;
                                           Language.mem := mem0;
                                           Language.pc := pc0;
                                           Language.ptr := ptr|} H2 H3)
                                           (Assembly.Swap)).
      (* easy *) admit.
      rewrite <- Heqq in *.
      assert (exists sqpc,
              @Common.to_nat (Compiler.comp_len prog) sqpc =
              (Common.to_nat (Assembly.pc q) + 1)).
      ssimpl.
      apply not_final with (spc := pc).
      assumption.
      destruct H7.
      rename x into sqpc.
      exists (Assembly.mkState _ _  (Assembly.prog q) (Assembly.mem q)
                                    (sqpc) (Assembly.b q)
                                    (Assembly.ac q)).
      ssimpl.
      (*TODO: show that q1's current instruction is Load*)
      destruct H6. rename x into q1.
      assert (exists q2, eval' q1 q2).
      admit.
      destruct H7. rename x into q2.
      assert (exists q3, eval' q2 q3).
      admit.
      destruct H8. rename x into q3.
      assert (exists q4, eval' q3 q4).
      admit.
      destruct H9. rename x into q4.
      assert (exists q5, eval' q4 q5).
      admit.
      destruct H10. rename x into q5.
      apply Common.t_trans with (y := q1). assumption.
      apply Common.t_trans with (y := q2). assumption.
      apply Common.t_trans with (y := q3). assumption.
      apply Common.t_trans with (y := q4). assumption.
      apply Common.t_trans with (y := q5). assumption.
      apply Common.t_base. admit.
    + (*same proof as before*) admit.

    (* will require other lemmas, as we will have to consider linking: *)
    + (*assert the existence of q1*) admit.
    + (*assert the existence of q1*) admit.
    + (*assert the existence of q1*) admit.
    + (*assert the existence of q1*) admit.
Admitted.
End Verification.