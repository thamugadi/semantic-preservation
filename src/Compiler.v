Require Import Common.
Require Import Language.
Require Import Assembly.

Require Import List.
Import List.ListNotations.

Module Compiler.

Fixpoint compile'' (p : Language.program) : Assembly.program :=
  match p with
  | [] => []
  | Language.PtrInc :: h => Assembly.Add 1 :: compile'' h
  | Language.PtrDec :: h => Assembly.Sub 1 :: compile'' h
  | Language.Inc :: h =>  Assembly.AddPtr 1 :: compile'' h
  | Language.Dec :: h =>  Assembly.SubPtr 1 :: compile'' h
  | Language.Jump :: h => Assembly.Skip   :: Assembly.UJUMP :: compile'' h
  | Language.Ret :: h =>  Assembly.Skip   :: Assembly.URET :: compile'' h
  | Language.Halt :: h => Assembly.Halt   :: compile'' h
  end.

Definition comp_first (x : Language.instr) : Assembly.instr :=
  match x with
  | Language.PtrInc => Assembly.Add 1
  | Language.PtrDec => Assembly.Sub 1
  | Language.Inc => Assembly.AddPtr 1
  | Language.Dec => Assembly.SubPtr 1
  | Language.Jump => Assembly.Skip
  | Language.Ret =>  Assembly.Skip
  | Language.Halt => Assembly.Halt
  end.

Fixpoint compile_index (p : Language.program) (x : nat) : nat :=
  match x with
  | 0 => 0
  | _ => match p with
         | [] => 0
         | Language.Jump :: h => 2 + compile_index h (x-1)
         | Language.Ret :: h => 2 + compile_index h (x-1)
         | _ :: h => 1 + compile_index h (x-1)
         end
  end.


Fixpoint nb_jump (p : Assembly.program) : nat :=
  match p with
  | [] => 0
  | Assembly.UJUMP :: t => 1 + nb_jump t
  | _ :: t => nb_jump t
  end.

Fixpoint nb_ret (p : Assembly.program) : nat :=
  match p with
  | [] => 0
  | Assembly.URET :: t => 1 + nb_ret t
  | _ :: t => nb_ret t
  end.

Fixpoint j_indexes (p : Assembly.program) : list nat :=
  match p with
  | [] => []
  | Assembly.UJUMP :: t => 0 :: map S (j_indexes t)
  | _ :: t => map S (j_indexes t)
  end.

Fixpoint r_indexes (p : Assembly.program) : list nat :=
  match p with
  | [] => []
  | Assembly.URET :: t => 0 :: map S (r_indexes t)
  | _ :: t => map S (r_indexes t)
  end.

(*

Put a at the p{^ th} place of v
Fixpoint replace {A n} (v : t A n) (p: Fin.t n) (a : A) {struct p}: t A n :=
*)

Fixpoint replace (v : list Assembly.instr) (p : nat) (a : Assembly.instr) : list Assembly.instr :=
  match v with
  | [] => v
  | h :: l => match p with
              | 0 => a :: l
              | S n => h :: replace l n a
              end
  end.

Fixpoint link_jump' (p : Assembly.program) (jumps rets : list nat) :
                    Assembly.program :=
  match jumps with
  | [] => p
  | a :: jumps' => match rets with
                  | [] => p
                  | r :: rets' => link_jump' (replace p a (Assembly.Jump r)) jumps' rets'
                  end
  end.

Fixpoint link_ret' (p : Assembly.program) (jumps rets : list nat) : Assembly.program :=
  match rets with
  | [] => p
  | a :: rets' => match jumps with
                  | [] => p
                  | r :: jumps' => link_ret' (replace p a (Assembly.Jump r)) jumps' rets'
                  end
  end.


Definition link_jump (p : Assembly.program) : (Assembly.program) :=
  link_jump' p (j_indexes p) (r_indexes p).


Fixpoint lj_indexes (p : Assembly.program) : list nat :=
  match p with
  | [] => []
  | Assembly.Jump _ :: t => 0 :: map S (lj_indexes t)
  | _ :: t => map S (lj_indexes t)
  end.

Definition link_ret (p : Assembly.program) : (Assembly.program) :=
  (link_ret' p (lj_indexes p) (r_indexes p)).

Definition inc_jump (i : Assembly.instr) : Assembly.instr :=
  match i with
  | Assembly.Jump n0 => Assembly.Jump (n0 + 1)
  | a => a
  end.

Fixpoint link_aux (l : Assembly.program) : Assembly.program :=
  match l with
  | [] => []
  | Assembly.UJUMP :: t => map (inc_jump) (link_ret (link_jump l))
  | Assembly.URET  :: t => map (inc_jump) (link_ret (link_jump l))
  | a :: t => a :: map inc_jump (link_aux t)
  end.

Definition link (l : Assembly.program) : Assembly.program :=
  map (inc_jump) (link_ret (link_jump l)).

Fixpoint map_aux (l : Assembly.program) : Assembly.program :=
  match l with
  | [] => []
  | Assembly.Jump n :: l' => Assembly.Jump (n+1) :: map_aux l'
  | a :: l' => a :: map_aux l'
  end.

Theorem map_eq : forall l, map_aux l = map (inc_jump) l.
Admitted.

Theorem link_eq : forall l, link l = link_aux l.
Admitted.

Definition compile' (p : Language.state) : Assembly.state :=
  Assembly.mkState (link (compile'' (Language.prog p)))
                   (Language.mem p)
                   (compile_index (Language.prog p) (Language.pc p))
                   (Language.ptr p).

Inductive compile (p : Language.state) (q : Assembly.state) : Prop :=
  | comp : q = compile' p -> compile p q.

End Compiler.
(*
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Extraction Language OCaml.
Recursive Extraction Compiler.compile'.
*)