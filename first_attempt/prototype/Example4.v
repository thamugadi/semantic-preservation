Require Import Vector.
Import Vector.VectorNotations.

Inductive instr :=
  | A : instr
  | B : instr
  | C : instr.


Definition vector_zip {A B : Type} {n : nat} (v1 : Vector.t A n)
                      (v2 : Vector.t B n) : Vector.t (A * B) n :=
  Vector.map2 (fun x y => (x, y)) v1 v2.

Check (5,5).

Fixpoint f' {n} (L : Vector.t (instr*instr) n) : Vector.t instr n :=
  match L with
  | [] => []
  | (A,h)::L' => h :: f' L'
  | (a,_)::L' => a :: f' L'
  end.

Definition f {n} (l : Vector.t instr n) (m : Vector.t instr n) :
                   Vector.t instr n := f' (vector_zip l m).



Theorem th : forall p ind, p[@ind] <> A ->
                           f p 