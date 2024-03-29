Require Import Common.
Require Import Language.
Require Import Assembly.
From Hammer Require Import Hammer.
From Hammer Require Import Tactics.
Require Import Vector.
Import Vector.VectorNotations.
Require Import Program.Equality.
Require Import PeanoNat.
Require Import Lia.
Import Nat.
Require Import Coq.Vectors.VectorEq.
Require Coq.Program.Wf.

Module Compiler.

Definition lenvec {A n} (v : Vector.t A n) : nat := n.
Fixpoint matched' {n} (p : Language.program n) (c : nat) : bool :=
  match c with
  | 0 => false
  | _ => match p with
    | [] => c =? 1
    | Language.Jump :: l => matched' l (c+1)
    | Language.Ret  :: l => matched' l (c-1)
    | _ :: l => matched' l c
    end
  end.


Inductive matched {n} (p : Language.program n) : Prop :=
  | match_r : matched' p 1 = true -> matched p.
Fixpoint comp_len {n} (p : Language.program n) : nat :=
  match p with
  | Vector.nil _ => 0
  | Language.PtrInc :: xs => 1 + comp_len xs
  | Language.PtrDec :: xs => 1 + comp_len xs
  | Language.Inc :: xs => 6 + comp_len xs
  | Language.Dec :: xs => 6 + comp_len xs
  | Language.Jump :: xs => 2 + comp_len xs
  | Language.Ret :: xs => 2 + comp_len xs
  | Language.Halt :: xs => 1 + comp_len xs
  end.

Fixpoint compile'' {n} (p : Language.program n) :
                          (Assembly.program (comp_len p)) :=
  match p with
  | [] => []
  | Language.PtrInc :: h => (Assembly.Add 1) :: compile'' h
  | Language.PtrDec :: h => (Assembly.Sub 1) :: compile'' h
  | Language.Inc :: h =>  Assembly.Swap   ::
                          Assembly.Load   ::
                          Assembly.Add 1  ::
                          Assembly.Store  ::
                          Assembly.Zero   ::
                          Assembly.Swap   :: compile'' h
  | Language.Dec :: h =>  Assembly.Swap   ::
                          Assembly.Load   ::
                          Assembly.Sub 1  ::
                          Assembly.Store  ::
                          Assembly.Zero   ::
                          Assembly.Swap   :: compile'' h

  | Language.Jump :: h => Assembly.Skip   ::
                          Assembly.UJUMP :: compile'' h
  | Language.Ret :: h =>  Assembly.Skip   ::
                          Assembly.URET :: compile'' h
  | Language.Halt :: h => Assembly.Halt   :: compile'' h
  end.

Definition compile_first {n : nat} (i : Language.instr) : Assembly.instr :=
  match i with
  | Language.PtrInc => Assembly.Add 1
  | Language.PtrDec => Assembly.Sub 1
  | Language.Inc => Assembly.Swap
  | Language.Dec => Assembly.Swap
  | Language.Jump => Assembly.Skip
  | Language.Ret => Assembly.Skip
  | Language.Halt => Assembly.Halt
  end.

Fixpoint compile_index {n} (p : Language.program n) (x : Fin.t n) 
                           : Fin.t (comp_len p).
Proof.
  destruct x eqn:H1; rewrite (eta p).
  - destruct hd; apply Fin.F1.
  - destruct hd.
    + do 1 apply Fin.FS. apply compile_index. exact t0.
    + do 1 apply Fin.FS. apply compile_index. exact t0.
    + do 6 apply Fin.FS. apply compile_index. exact t0.
    + do 6 apply Fin.FS. apply compile_index. exact t0.
    + do 2 apply Fin.FS. apply compile_index. exact t0.
    + do 2 apply Fin.FS. apply compile_index. exact t0.
    + do 1 apply Fin.FS. apply compile_index. exact t0.
Defined.

Fixpoint nb_jump {n} (p : Assembly.program n) : nat :=
  match p with
  | [] => 0
  | Assembly.UJUMP :: t => 1 + nb_jump t
  | _ :: t => nb_jump t
  end.

Fixpoint nb_ret {n} (p : Assembly.program n) : nat :=
  match p with
  | [] => 0
  | Assembly.URET :: t => 1 + nb_ret t
  | _ :: t => nb_ret t
  end.

Fixpoint j_indexes {n} (p : Assembly.program n) 
                       : (Vector.t (Fin.t n) (nb_jump p)) :=
  match p with
  | [] => []
  | Assembly.UJUMP :: t => Fin.F1 :: map Fin.FS (j_indexes t)
  | _ :: t => map Fin.FS (j_indexes t)
  end.

Fixpoint r_indexes {n} (p : Assembly.program n) 
                       : (Vector.t (Fin.t n) (nb_ret p)) :=
  match p with
  | [] => []
  | Assembly.URET :: t => Fin.F1 :: map Fin.FS (r_indexes t)
  | _ :: t => map Fin.FS (r_indexes t)
  end.

  

Fixpoint link_jump' {n ln ln'} (p : Assembly.program n) 
                          (jumps : Vector.t (Fin.t n) ln)
                          (rets : Vector.t (Fin.t n) ln') :
                          Assembly.program n :=
  match jumps with
  | [] => p
  | a :: jumps' => match rets with
                  | [] => p
                  | r :: rets' => link_jump' 
                                  (replace p a (Assembly.Jump 
                                  (Common.to_nat r)))
                                  jumps' rets'
                  end
  end.


Definition link_jump {n} (p : Assembly.program n) : (Assembly.program n) :=
  link_jump' p (j_indexes p) (r_indexes p).

Fixpoint nb_ljump {n} (p : Assembly.program n) : nat :=
  match p with
  | [] => 0
  | Assembly.Jump _ :: t => 1 + nb_ljump t
  | _ :: t => nb_ljump t
  end.


Fixpoint lj_indexes {n} (p : Assembly.program n) 
                        : (Vector.t (Fin.t n) (nb_ljump p)) :=
  match p with
  | [] => []
  | Assembly.Jump _ :: t => Fin.F1 :: map Fin.FS (lj_indexes t)
  | _ :: t => map Fin.FS (lj_indexes t)
  end.


Definition make_f1 (x : nat) (H : x <> 0) : Fin.t x.
Proof.
  destruct x eqn:H1.
  - auto with *.
  - exact Fin.F1.
Defined.

Fixpoint weaken_fin_t {n : nat} (f : Fin.t n) : Fin.t (S n) :=
  match f in Fin.t n return Fin.t (S n) with
  | Fin.F1 => Fin.F1
  | Fin.FS f' => Fin.FS (weaken_fin_t f')
  end.

Fixpoint make_indexes (n : nat) : Vector.t (Fin.t n) n :=
  match n with
  | 0 => []
  | S i => Fin.F1 :: map Fin.FS (make_indexes i)
  end.

Fixpoint link_ret' {n ln ln'} (p : Assembly.program n) 
                          (jumps : Vector.t (Fin.t n) ln) 
                          (rets : Vector.t (Fin.t n) ln') :
                          Assembly.program n :=
  match rets with
  | [] => p
  | a :: rets' => match jumps with
                  | [] => p
                  | r :: jumps' => link_ret' (replace p a 
                                   (Assembly.Jump (Common.to_nat r)))
                                   jumps' rets'
                  end
  end.

Definition inc_jump (i : Assembly.instr) : Assembly.instr :=
  match i with
  | Assembly.Jump n0 => Assembly.Jump (n0 + 1)
  | a => a
  end.

Definition link_ret {n} (p : Assembly.program n) : (Assembly.program n) :=
  (link_ret' p (lj_indexes p) (r_indexes p)).

Definition link {n} (l : Assembly.program n) : (Assembly.program n) :=
  map (inc_jump) (link_ret (link_jump l)).

Definition make_vector (A : Type) (x : A) (n : nat) : Vector.t A n.
Proof.
  induction n.
  - apply Vector.nil.
  - apply Vector.cons.
    + exact x.
    + exact IHn.
Defined.

Lemma lm1 {n m} : forall p, n <> 0 -> comp_len (@Language.prog n m p) <> 0.
Proof.
  intros.
  destruct p.
  cbn.
  destruct prog.
  inversion pc.
  unfold not. intros.
  destruct h; inversion H0.
Qed.

Definition compile' {n m}
  (p : Language.state (n := n)) (HA: n <> 0) (HA2 : m <> 0) : 
  (Assembly.state (n := comp_len p.(Language.prog)) (m := m)) :=
  let newlen := comp_len p.(Language.prog) in
  let newpc := compile_index p.(Language.prog) p.(Language.pc) in
  let f1_index := make_f1 (comp_len p.(Language.prog)) (lm1 p HA) in
  let f1_mem := make_f1 m HA2 in
  @Assembly.mkState newlen m (compile'' p.(Language.prog)) p.(Language.mem)
   newpc p.(Language.ptr) f1_mem.

Definition compile_link {n m} (p : Language.state (n := n)) (HA : n <> 0)
                              (HA2 : m <> 0) : 
  (Assembly.state (n := comp_len p.(Language.prog)) (m := m)) :=
  let cpl := compile' p HA HA2 in
  Assembly.mkState (comp_len (Language.prog p)) m (link cpl.(Assembly.prog))
                   cpl.(Assembly.mem)
  cpl.(Assembly.pc) cpl.(Assembly.ac) cpl.(Assembly.b).

Inductive compile {n m}
  (p : Language.state (n := n))
  (q : Assembly.state (n := comp_len p.(Language.prog)) (m := m)) : Prop :=
  | comp_r : forall H H1, matched (p.(Language.prog)) -> q 
             = compile_link p H H1 -> compile p q.
End Compiler.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Extraction Language OCaml.
Recursive Extraction Compiler.compile_link.