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
Lemma link_stable : forall n p ind i, (i <> Assembly.UJUMP /\ i <> Assembly.URET) ->
                    p[@ind] = i -> (@Compiler.link n p)[@ind] = i.
Proof.
Admitted.

Lemma read_comp {n m} : forall p i H1 H2, Language.read_instr p i ->
                               i <> Language.Jump -> i <> Language.Ret ->
                               Assembly.read_instr (@Compiler.compile_link n m p H1 H2)
                               (@Compiler.compile_first n i).
Proof.
  unfold Compiler.compile_link.
  unfold Compiler.compile'.
  intros.
  ssimpl.
  apply Assembly.ri.
  unfold Assembly.read_instr'. simpl.
  assert ((Compiler.compile'' prog)[@Compiler.compile_index prog pc] =
  @Compiler.compile_first n prog[@pc]).
  apply read_instr_eq.
  apply link_stable.
  ssimpl.
  - unfold Compiler.compile_first in H4.
    qsimpl.
  - unfold Compiler.compile_first in H4.
    qsimpl.
  - qsimpl.
Qed.

Lemma to_nat_st {n} : forall a b, @Common.to_nat n a = Common.to_nat b -> a = b.
Proof.
  intros.
  dependent induction a; dependent destruction b.
  reflexivity.
  assert (n = 0). ssimpl. exfalso. ssimpl.
  assert (n = 0). ssimpl. exfalso. ssimpl.
  f_equal.
  apply IHa.
  inversion H.
  reflexivity.
Qed.

Fixpoint weaken_fin_t {n : nat} (f : Fin.t n) : Fin.t (S n) :=
  match f in Fin.t n return Fin.t (S n) with
  | Fin.F1 => Fin.F1
  | Fin.FS f' => Fin.FS (weaken_fin_t f')
  end.

Definition safe_fs {n} (i : Fin.t n) (H : (Common.to_nat i) + 1 <> n) : Fin.t n.
Proof.
  intros.
  destruct n. inversion i.
  pose (X := Fin.of_nat (Common.to_nat i + 1) (S n)).
  destruct X eqn:A.
  exact t0.
  sfirstorder.
Defined.

Lemma fs_lm : forall n i, @Common.to_nat n i <> n.
Proof.
  intros.
  induction i, n.
  - simpl. lia.
  - simpl. lia.
  - inversion i.
  - sfirstorder.
Qed.

Lemma safe_fs_is_s {n} : forall i H,
                         @Common.to_nat n (safe_fs i H) = (Common.to_nat i) + 1.
Proof.
  intros.
  induction i, n.
  - simpl in H. lia.
  - now reflexivity.
  - inversion i.
  - hauto.
Qed.

Lemma not_final_lm1 {n} : forall prog pc pc',
                          (@Common.to_nat n pc) + 1 = @Common.to_nat n pc' ->
                          Common.to_nat (Compiler.compile_index prog pc) + 1 <>
                          Compiler.comp_len prog.
Proof.
  intros;
  assert (Common.to_nat pc' <> n) by apply fs_lm;
  rewrite <- H in H0;
  induction pc; dependent destruction pc'; dependent destruction prog.
  - sfirstorder.
  - simpl; dependent destruction pc'; dependent destruction prog; qsimpl.
  - simpl in H; inversion H.
  - ssimpl; (apply IHpc with (prog := prog) (pc' := pc'); (try assumption);
    try hauto).
Qed.
 
Lemma not_final {n} : forall pc prog spc,
                     (Common.to_nat pc) + 1 = @Common.to_nat n spc ->
                     exists sqpc, @Common.to_nat (Compiler.comp_len prog) sqpc =
                     (Common.to_nat (@Compiler.compile_index n prog pc) + 1).
Proof.
  intros.
  assert (Common.to_nat (@Compiler.compile_index n prog pc) + 1 
          <> Compiler.comp_len prog).
  apply not_final_lm1 with (pc' := spc); assumption.
  exists (safe_fs (@Compiler.compile_index n prog pc) H0); 
  apply safe_fs_is_s.
Qed.

Lemma compiled_pc : forall n prog pc pc0 i, Language.read_instr' prog pc0 = i ->
                    Common.to_nat pc0 + 1 = Common.to_nat pc ->
                    Common.to_nat (Compiler.compile_index prog pc0) +
                    vec_len (Compiler.compile'' [i])
                    = Common.to_nat (@Compiler.compile_index n prog pc).
Proof.
  intros.
  unfold vec_len.
  unfold Language.read_instr' in *.
  induction pc0; dependent destruction pc; dependent destruction prog.
  - sfirstorder.
  - ssimpl; dependent destruction pc; dependent destruction prog; ssimpl.
  - simpl in H. destruct i; destruct h; ssimpl.
  - simpl in H. destruct h; destruct i; hauto; do 6 f_equal; assumption. 
Qed.

Theorem seq_instr {n} : forall p x x'
                  (off : Fin.t (Compiler.comp_len ([p[@x]]))),
                  Common.to_nat x' =
                  Common.to_nat (@Compiler.compile_index n p x) + Common.to_nat off ->
                  (Compiler.compile'' p)[@x'] = (Compiler.compile'' [p[@x]])[@off].
Proof.
Admitted.

Ltac seq_ins_n p pc' n H :=
  intros;
  destruct p as [prog mem pc ptr];
  unfold Compiler.compile_link in *;
  apply Assembly.ri;
  unfold Assembly.read_instr' in *;
  simpl in *;
  destruct H; try ssimpl;
  apply link_stable; try sdone;
  assert (Compiler.comp_len [prog[@pc]] <> 0) as EH2;
  try qauto;
  pose (X := Common.make_fn (Compiler.comp_len [prog[@pc]]) n EH2);
  assert ((Compiler.compile'' prog)[@pc'] = (Compiler.compile'' [prog[@pc]])[@X]) as EH;
  try (apply seq_instr); hauto.

Lemma seq_inc1 {n m}: forall p q1 H H',
                     (Language.prog p)[@Language.pc p] = Language.Inc ->
                     Assembly.read_instr (Compiler.compile_link p H H') Assembly.Swap ->
                     eval' (@Compiler.compile_link n m p H H') q1 ->
                     Assembly.read_instr q1 Assembly.Load.
Proof.
  seq_ins_n p pc0 1 H2.
Qed.

Lemma seq_inc2 {n m}: forall p q1 q2 H H',
                     (Language.prog p)[@Language.pc p] = Language.Inc ->
                     Assembly.read_instr (Compiler.compile_link p H H') Assembly.Swap ->
                     eval' (@Compiler.compile_link n m p H H') q1 ->
                     eval' q1 q2 -> Assembly.read_instr q1 Assembly.Load ->
                     Assembly.read_instr q2 (Assembly.Add 1).
Proof.
  seq_ins_n p pc0 2 H3.
Qed.

Lemma seq_inc3 {n m}: forall p q1 q2 q3 H H',
                     (Language.prog p)[@Language.pc p] = Language.Inc ->
                     Assembly.read_instr (Compiler.compile_link p H H') Assembly.Swap ->
                     eval' (@Compiler.compile_link n m p H H') q1 ->
                     eval' q1 q2 -> eval' q2 q3 -> Assembly.read_instr q1 Assembly.Load ->
                     Assembly.read_instr q2 (Assembly.Add 1) ->
                     Assembly.read_instr q3 (Assembly.Store).
Proof.
  seq_ins_n p pc0 3 H4.
Qed.
Lemma seq_inc4 {n m}: forall p q1 q2 q3 q4 H H',
                     (Language.prog p)[@Language.pc p] = Language.Inc ->
                     Assembly.read_instr (Compiler.compile_link p H H') Assembly.Swap ->
                     eval' (@Compiler.compile_link n m p H H') q1 ->
                     eval' q1 q2 -> eval' q2 q3 -> eval' q3 q4 ->
                     Assembly.read_instr q1 Assembly.Load ->
                     Assembly.read_instr q2 (Assembly.Add 1) ->
                     Assembly.read_instr q3 (Assembly.Store) ->
                     Assembly.read_instr q4 (Assembly.Zero).
Proof.
  (*seq_ins_n p pc0 4 H5.*) (*works, but too slow*)
Admitted.
Lemma seq_inc5 {n m}: forall p q1 q2 q3 q4 q5 H H',
                     (Language.prog p)[@Language.pc p] = Language.Inc ->
                     Assembly.read_instr (Compiler.compile_link p H H') Assembly.Swap ->
                     eval' (@Compiler.compile_link n m p H H') q1 ->
                     eval' q1 q2 -> eval' q2 q3 -> eval' q3 q4 -> eval' q4 q5 ->
                     Assembly.read_instr q1 Assembly.Load ->
                     Assembly.read_instr q2 (Assembly.Add 1) ->
                     Assembly.read_instr q3 (Assembly.Store) ->
                     Assembly.read_instr q4 (Assembly.Zero) ->
                     Assembly.read_instr q5 (Assembly.Swap).
Proof.
  (*seq_ins_n p pc0 5 H6.*) (*too slow*)
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
    (*Assembly.PtrInc*)
    + apply Common.t_base.
      apply Assembly.add with (n' := 1).
      * assert (Assembly.read_instr (@Compiler.compile_link n m {|Language.prog := prog;
       Language.mem := mem;
       Language.pc := pc0;
       Language.ptr := ptr0|} H2 H3) (Assembly.Add 1)).
       apply read_comp with (i := Language.PtrInc). ssimpl.
       discriminate. discriminate.
       assumption.
      * simpl.
        unfold Common.to_nat.
        apply compiled_pc with (i := Language.PtrInc); assumption.
      * now reflexivity.
      * now reflexivity.
      * simpl. unfold Compiler.make_f1. ssimpl.
      * ssimpl.
    (*Assembly.PtrDec*)
    + apply Common.t_base.
      apply Assembly.sub with (n' := 1).
      * assert (Assembly.read_instr (@Compiler.compile_link n m {|Language.prog := prog;
       Language.mem := mem;
       Language.pc := pc0;
       Language.ptr := ptr0|} H2 H3) (Assembly.Sub 1)).
       apply read_comp with (i := Language.PtrDec). ssimpl.
       discriminate. discriminate.
       assumption.
      * simpl.
        apply compiled_pc with (i := Language.PtrDec); assumption.
      * now reflexivity.
      * now reflexivity.
      * simpl. unfold Compiler.make_f1. ssimpl.
      * ssimpl.

    (*Assembly.Inc*)
    + remember (Compiler.compile_link {|Language.prog := prog;Language.mem := mem0;
               Language.pc := pc0; Language.ptr := ptr|} H2 H3) as q.
      remember (Compiler.compile_link {|Language.prog := prog;Language.mem := mem;
               Language.pc := pc; Language.ptr := ptr|} H0 H1) as q'.
      assert (prog[@pc0] = Language.Inc). ssimpl.
      assert (Compiler.compile'' [Language.Inc] =
             [Assembly.Swap; Assembly.Load; Assembly.Add 1;
             Assembly.Store;Assembly.Zero; Assembly.Swap]).
      now reflexivity.

      assert (Assembly.read_instr 
             (@Compiler.compile_link n m {|Language.prog := prog;
                                           Language.mem := mem0;
                                           Language.pc := pc0;
                                           Language.ptr := ptr|} H2 H3)
                                           (Assembly.Swap)).
      apply read_comp with (i := Language.Inc).
      ssimpl.
      discriminate. discriminate.
(**)
      assert (exists q1, eval' q q1).
      rewrite <- Heqq in *.
      assert (exists sqpc,
              @Common.to_nat (Compiler.comp_len prog) sqpc =
              (Common.to_nat (Assembly.pc q) + 1)).
      ssimpl.
      apply not_final with (spc := pc).
      assumption.
      destruct H7; rename x into sqpc.
      exists (Assembly.mkState _ _  (Assembly.prog q) (Assembly.mem q)
                                    (sqpc) (Assembly.b q)
                                    (Assembly.ac q)).
      ssimpl.
      destruct H7; rename x into q1.

      assert (Assembly.read_instr q1 Assembly.Load).
      apply seq_inc1 with (H := H2) (H' := H3); ssimpl.
      assert (exists q2, eval' q1 q2).
      admit.
      destruct H9; rename x into q2.
      assert (Assembly.read_instr q2 (Assembly.Add 1)).
      admit.
      assert (exists q3, eval' q2 q3).
      admit.
      destruct H11; rename x into q3.
      assert (Assembly.read_instr q3 Assembly.Store).
      admit.
      assert (exists q4, eval' q3 q4).
      admit.
      destruct H13; rename x into q4.
      assert (Assembly.read_instr q4 Assembly.Zero).
      admit.
      assert (exists q5, eval' q4 q5).
      admit.
      destruct H15; rename x into q5.
      assert (Assembly.read_instr q5 Assembly.Swap).
      admit.
      apply Common.t_trans with (y := q1). assumption.
      apply Common.t_trans with (y := q2). assumption.
      apply Common.t_trans with (y := q3). assumption.
      apply Common.t_trans with (y := q4). assumption.
      apply Common.t_trans with (y := q5). assumption.
      apply Common.t_base.
      apply Assembly.swap.
      * assumption.
      * assert (Assembly.prog q = Assembly.prog q').
        ssimpl.
        assert (Assembly.prog q1 = Assembly.prog q). inversion H7; qsimpl.
        assert (Assembly.prog q2 = Assembly.prog q1). inversion H9; qsimpl.
        assert (Assembly.prog q3 = Assembly.prog q2). inversion H11; qsimpl.
        assert (Assembly.prog q4 = Assembly.prog q3). inversion H13; qsimpl.
        assert (Assembly.prog q5 = Assembly.prog q4). inversion H15; qsimpl.
        qsimpl.
      * admit.
      * admit.
      * admit.
      * admit.

    + (*same proof as before*) 
      (*Assembly.Dec*) 
      admit.
    + (*Assembly.Jump, resulting from two cases of Jump and two cases of Ret*)
      (* will require other lemmas, as we will have to consider linking: *)
      (*assert the existence of q1*)
      admit.
    + (*assert the existence of q1*)
      admit.
    + (*assert the existence of q1*) 
      admit.
    + (*assert the existence of q1*)
      admit.
Admitted.
End Verification.