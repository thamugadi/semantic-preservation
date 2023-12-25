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

Fixpoint compile''_ {n n'} (p : Language.program n) :
                          (Assembly.program' (comp_len p) n') :=
  match p with
  | [] => []
  | Language.PtrInc :: h => (Assembly.Add 1) :: compile''_ h
  | Language.PtrDec :: h => (Assembly.Sub 1) :: compile''_ h
  | Language.Inc :: h =>  Assembly.Swap   ::
                          Assembly.Load   ::
                          Assembly.Add 1  ::
                          Assembly.Store  ::
                          Assembly.Zero   ::
                          Assembly.Swap   :: compile''_ h
  | Language.Dec :: h =>  Assembly.Swap   ::
                          Assembly.Load   ::
                          Assembly.Sub 1  ::
                          Assembly.Store  ::
                          Assembly.Zero   ::
                          Assembly.Swap   :: compile''_ h

  | Language.Jump :: h => Assembly.Skip   ::
                          Assembly.UJUMP :: compile''_ h
  | Language.Ret :: h =>  Assembly.Skip   ::
                          Assembly.URET :: compile''_ h
  | Language.Halt :: h => Assembly.Halt   :: compile''_ h
  end.

Definition compile_one {n : nat} (i : Language.instr) : @Assembly.program (comp_len [i]) :=
  match i with
  | Language.PtrInc => [Assembly.Add 1]
  | Language.PtrDec => [Assembly.Sub 1]
  | Language.Inc => [Assembly.Swap; Assembly.Load; Assembly.Add 1; Assembly.Store; Assembly.Zero; Assembly.Swap]
  | Language.Dec => [Assembly.Swap; Assembly.Load; Assembly.Sub 1; Assembly.Store; Assembly.Zero; Assembly.Swap]
  | Language.Jump => [Assembly.Skip; Assembly.UJUMP]
  | Language.Ret => [Assembly.Skip; Assembly.URET]
  | Language.Halt => [Assembly.Halt]
  end.

Definition compile_first {n : nat} (i : Language.instr) : Assembly.instr (n:=n) :=
  match i with
  | Language.PtrInc => Assembly.Add 1
  | Language.PtrDec => Assembly.Sub 1
  | Language.Inc => Assembly.Swap
  | Language.Dec => Assembly.Swap
  | Language.Jump => Assembly.Skip
  | Language.Ret => Assembly.Skip
  | Language.Halt => Assembly.Halt
  end.
Definition compile'' {n} (p : Language.program n) : (Assembly.program (comp_len p)) := 
  @compile''_ n (comp_len p) p.

Fixpoint compile_index {n} (p : Language.program n) (x : Fin.t n) : Fin.t (comp_len p).
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

Fixpoint nb_jump' {n n'} (p : Assembly.program' n n') : nat :=
  match p with
  | [] => 0
  | Assembly.UJUMP :: t => 1 + nb_jump' t
  | _ :: t => nb_jump' t
  end.

Definition nb_jump {n} (p : Assembly.program n) : nat := @nb_jump' n n p.

Fixpoint nb_ret' {n n'} (p : Assembly.program' n n') : nat :=
  match p with
  | [] => 0
  | Assembly.URET :: t => 1 + nb_ret' t
  | _ :: t => nb_ret' t
  end.

Definition nb_ret {n} (p : Assembly.program n) : nat := @nb_ret' n n p.

Definition vector_zip {A B : Type} {n : nat} (v1 : Vector.t A n) (v2 : Vector.t B n) : Vector.t (A * B) n :=
  Vector.map2 (fun x y => (x, y)) v1 v2.


Fixpoint j_indexes' {n n'} (p : Assembly.program' n n') : (Vector.t (Fin.t n) (nb_jump' p)) :=
  match p with
  | [] => []
  | Assembly.UJUMP :: t => Fin.F1 :: map Fin.FS (j_indexes' t)
  | _ :: t => map Fin.FS (j_indexes' t)
  end.

Definition j_indexes {n} (p : Assembly.program n) : Vector.t (Fin.t n) (nb_jump p) :=
  j_indexes' p.

Fixpoint r_indexes' {n n'} (p : Assembly.program' n n') : (Vector.t (Fin.t n) (nb_ret' p)) :=
  match p with
  | [] => []
  | Assembly.URET :: t => Fin.F1 :: map Fin.FS (r_indexes' t)
  | _ :: t => map Fin.FS (r_indexes' t)
  end.

Definition r_indexes {n} (p : Assembly.program n) : Vector.t (Fin.t n) (nb_ret p) :=
  r_indexes' p.

Fixpoint link_jump' {n ln ln'} (p : Assembly.program n) 
                          (jumps : Vector.t (Fin.t n) ln) (rets : Vector.t (Fin.t n) ln') :
                          Assembly.program n :=
  match jumps with
  | [] => p
  | a :: jumps' => match rets with
                  | [] => p
                  | r :: rets' => link_jump' (replace p a (Assembly.Jump r)) jumps' rets'
                  end
  end.


Definition link_jump {n} (p : Assembly.program n) : (Assembly.program n) :=
  link_jump' p (j_indexes p) (r_indexes p).

Check pred.
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

Definition make_ind_v {n A} (v : Vector.t A n) : Vector.t (A*(Fin.t n)) n :=
  vector_zip v (make_indexes n).

Fixpoint link_ret' {n n'} (p : Vector.t (@Assembly.instr n * (Fin.t n)) n') (p' : Assembly.program n) : Assembly.program n :=
  match p with
  | [] => p'
  | (Assembly.Jump i, ind) :: t => link_ret' t (replace p' i (Assembly.Jump ind))
  | (_, ind) :: t => link_ret' t p'
  end.

(*Cannot guess decreasing argument of fix.*)

Definition link_ret {n} (p : Assembly.program n) : Assembly.program n := link_ret' (make_ind_v p) p.

Definition link {n} (l : Assembly.program n) : (Assembly.program n) := link_ret (link_jump l) .

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
  @Assembly.mkState newlen m (compile'' p.(Language.prog)) p.(Language.mem) newpc p.(Language.ptr) f1_mem.

Definition compile_link {n m} (p : Language.state (n := n)) (HA : n <> 0) (HA2 : m <> 0) : 
  (Assembly.state (n := comp_len p.(Language.prog)) (m := m)) :=
  let cpl := compile' p HA HA2 in
  Assembly.mkState (comp_len (Language.prog p)) m (link cpl.(Assembly.prog)) cpl.(Assembly.mem) cpl.(Assembly.pc) cpl.(Assembly.ac) cpl.(Assembly.b).

Inductive compile {n m}
  (p : Language.state (n := n))
  (q : Assembly.state (n := comp_len p.(Language.prog)) (m := m)) : Prop :=
  | comp_r : forall H H1, matched (p.(Language.prog)) -> q = compile_link p H H1 -> compile p q.
End Compiler.