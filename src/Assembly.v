Require Import Vector.
Import Vector.VectorNotations.
Require Import Program.Equality.
Require Import Common.
Module Assembly.

Inductive instr {n} : Type :=
  | Load : instr
  | Store : instr
  | Add : nat -> instr
  | Sub : nat -> instr
  | Jump : (Fin.t n) -> instr
  | Skip : instr
  | Swap : instr
  | Zero : instr
  | Halt : instr
  | UJUMP : instr (* unlinked *)
  | URET : instr (* unlinked *).

Definition program' (n : nat) (n' : nat) := t (@instr n') n.
Definition program (n : nat) := program' n n. 
Record state {n m : nat} : Type := mkState
{ 
  prog : @program n;
  mem : t nat m;
  pc : Fin.t n;
  ac : Fin.t m;
  b : Fin.t m;
}.

Definition read_instr' {n} (prog : @program n) (pc : Fin.t n) : instr := prog[@pc].

Inductive read_instr {n m} (p : state) (i : instr) : Prop :=
  | ri : read_instr' p.(prog n m) p.(pc) = i -> read_instr p i.

Definition read_mem' {m} (mem : t nat m) (ptr : Fin.t m) : nat := mem[@ptr].

Inductive read_mem {n m} (p : state) (e : nat) : Prop  :=
  | mi : read_mem' p.(mem n m) p.(ac) = e -> read_mem p e.

Inductive mem_diff {m} (m1 : t nat m) (m2 : t nat m) (x : Fin.t m) : Prop :=
  | md : (forall i, i <> x -> m2[@i] = m1[@i]) -> mem_diff m1 m2 x. 

Fixpoint to_nat {n} (x : Fin.t n) : nat.
Proof.
  destruct x eqn:H.
  - exact 0.
  - apply plus.
    + exact 1.
    + apply to_nat with (n := n).
      exact t.
Defined.

Fixpoint weaken_fin_t {n : nat} (f : Fin.t n) : Fin.t (S n) :=
  match f in Fin.t n return Fin.t (S n) with
  | Fin.F1 => Fin.F1
  | Fin.FS f' => Fin.FS (weaken_fin_t f')
  end.

(* Small-step operational semantics for our target language.*)

Inductive semantics {n m} (p : state) (p' : state) : Prop :=
  | load : read_instr p (Load) ->  to_nat p.(pc n m) + 1 = to_nat p'.(pc)->
             p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) -> p.(b) = p'.(b) ->
             to_nat p'.(ac) = (read_mem' p.(mem) p.(b)) -> semantics p p'
  | store: read_instr p (Store) -> to_nat p.(pc) + 1 = to_nat p'.(pc) ->
           p.(prog) = p'.(prog) -> p.(ac) = p'.(ac) ->
           to_nat p.(ac) = read_mem' p'.(mem) p.(ac) -> p.(b) = p'.(b) ->
           mem_diff p.(mem) p'.(mem) p.(b) -> semantics p p'
  | add : forall n', read_instr p (Add n') -> to_nat p.(pc) + 1 = to_nat p'.(pc) ->
              p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) -> p.(b) = p'.(b) ->
              to_nat p'.(ac) = to_nat (p.(ac)) + n' -> semantics p p'
  | sub : forall n', read_instr p (Sub n') -> to_nat p.(pc) + 1 = to_nat p'.(pc) ->
              p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) -> p.(b) = p'.(b) ->
              to_nat p'.(ac) = (to_nat p.(ac)) - n' -> semantics p p'
  | jump : forall n', read_instr p (Jump n') -> p.(prog) = p'.(prog) ->
               p.(ac) = p'.(ac) -> p.(mem) = p'.(mem) -> weaken_fin_t (p'.(pc)) = Fin.FS n' -> p.(b) = p'.(b) -> semantics p p'
  | skipz: read_instr p (Skip) -> p.(prog) = p'.(prog) ->
               p.(mem) = p'.(mem) -> p.(ac) = p'.(ac) -> p.(b) = p'.(b) ->
               read_mem p 0 -> to_nat (p'.(pc)) = to_nat (p.(pc)) + 2 -> semantics p p'
  | skipnz: read_instr p (Skip) -> p.(prog) = p'.(prog) ->
                p.(mem) = p'.(mem) -> p.(ac) = p'.(ac) -> p.(b) = p'.(b) ->
                ~ (read_mem p 0) -> to_nat p'.(pc) = (to_nat p.(pc)) + 1 -> semantics p p'
  | swap : read_instr p (Swap) -> p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
           p.(ac) = p'.(b) -> p.(b) = p'.(ac) -> to_nat p'.(pc) = (to_nat p.(pc)) + 1 ->
           semantics p p'
  | zero : read_instr p (Zero) -> p.(prog) = p'.(prog) -> p.(mem) = p'.(mem) ->
           p'.(b) = p.(b) -> 0 = to_nat p'.(ac) -> to_nat p'.(pc) = (to_nat p.(pc)) + 1 ->
           semantics p p'.
End Assembly.