Require Import Common. 
Module Simulation.

Definition lockstep_backward_sim {A : Type} {B : Type} 
  (compile : A -> B -> Prop)
  (eval : A -> A -> Prop)
  (eval': B -> B -> Prop) := 
    forall p q, compile p q ->
    forall q', eval' q q' -> 
    exists p', eval p p' /\ compile p' q'.

Definition lockstep_bisim {A : Type} {B : Type} 
  (compile : A -> B -> Prop)
  (eval : A -> A -> Prop)
  (eval': B -> B -> Prop) := 
    forall p q, compile p q ->
    (forall p', eval p p' -> 
    exists q', eval' q q' /\ compile p' q') /\
    (forall q', eval' q q' -> 
    exists p', eval p p' /\ compile p' q').

Definition plus_forward_sim {A : Type} {B : Type}
  (compile : A -> B -> Prop)
  (eval : A -> A -> Prop)
  (eval': B -> B -> Prop) :=
    forall p q, compile p q ->
    forall p', eval p p' ->
    exists q', (Common.plus eval') q q' /\ compile p' q'.

Definition plus_backward_sim {A : Type} {B : Type}
  (compile : A -> B -> Prop)
  (eval : A -> A -> Prop)
  (eval': B -> B -> Prop) :=
    forall p q, compile p q ->
    forall q', eval' q q' ->
    exists p', (Common.plus eval) p p' /\ compile p' q'.

Definition plus_bisim {A : Type} {B : Type} 
  (compile : A -> B -> Prop)
  (eval : A -> A -> Prop)
  (eval': B -> B -> Prop) := 
    forall p q, compile p q ->
    (forall p', eval p p' -> 
    exists q', (Common.plus eval') q q' /\ compile p' q') /\
    (forall q', eval' q q' -> 
    exists p', (Common.plus eval) p p' /\ compile p' q').

Definition star_forward_sim {A : Type} {B : Type} {Ord : Type}
  (measure : A -> Ord)
  (order_R : Ord -> Ord -> Prop) 
  (compile : A -> B -> Prop)
  (eval : A -> A -> Prop)
  (eval': B -> B -> Prop) :=
    forall p q, compile p q ->
    (forall p', eval p p' ->
    exists q', (Common.plus eval') q q' /\ compile p' q') \/
    (forall p', eval p p' /\ order_R (measure p') (measure p) ->
    exists q', (Common.star eval') q q' /\ compile p' q').

Definition star_backward_sim {A : Type} {B : Type} {Ord : Type}
  (measure : B -> Ord)
  (order_R : Ord -> Ord -> Prop) 
  (compile : A -> B -> Prop)
  (eval : A -> A -> Prop)
  (eval': B -> B -> Prop) :=
    forall p q, compile p q ->
    (forall q', eval' q q' ->
    exists p', (Common.plus eval) p p' /\ compile p' q') \/
    (forall q', eval' q q' /\ order_R (measure q') (measure q) ->
    exists p', (Common.star eval) p p' /\ compile p' q').

Definition star_bisim {A : Type} {B : Type} {Ord : Type} {Ord' : Type}
  (measure : A -> Ord)
  (measure' : B -> Ord')
  (order_R : Ord -> Ord -> Prop)
  (order_R' : Ord' -> Ord' -> Prop)
  (compile : A -> B -> Prop)
  (eval : A -> A -> Prop)
  (eval': B -> B -> Prop) :=
    forall p q, compile p q ->
    ((forall p', eval p p' ->
    exists q', (Common.plus eval') q q' /\ compile p' q') \/
    (forall p', eval p p' /\ order_R (measure p') (measure p) ->
    exists q', (Common.star eval') q q' /\ compile p' q')) /\
    ((forall q', eval' q q' ->
    exists p', (Common.plus eval) p p' /\ compile p' q') \/
    (forall q', eval' q q' /\ order_R' (measure' q') (measure' q) ->
    exists p', (Common.star eval) p p' /\ compile p' q')).

Definition option_forward_sim {A : Type} {B : Type} {Ord : Type}
  (empty : (A -> A -> Prop) -> (A -> A -> Prop))
  (measure : A -> Ord)
  (order_R : Ord -> Ord -> Prop) 
  (compile : A -> B -> Prop)
  (eval : A -> A -> Prop)
  (eval': B -> B -> Prop) :=
    forall p q, compile p q ->
    (forall p', eval p p' ->
    exists q', eval' q q' /\ compile p' q') \/
    (forall p', (empty eval) p p' /\ order_R (measure p') (measure p) ->
    compile p' q).

Definition option_backward_sim {A : Type} {B : Type} {Ord : Type}
  (empty : (B -> B -> Prop) -> (B -> B -> Prop))
  (measure : B -> Ord)
  (order_R : Ord -> Ord -> Prop) 
  (compile : A -> B -> Prop)
  (eval : A -> A -> Prop)
  (eval': B -> B -> Prop) :=
    forall p q, compile p q ->
    (forall q', eval' q q' ->
    exists p', eval p p' /\ compile p' q') \/
    (forall q', (empty eval') q q' /\ order_R (measure q') (measure q) ->
    compile p q').

Definition option_bisim {A : Type} {B : Type} {Ord : Type} {Ord' : Type}
  (empty : (A -> A -> Prop) -> (A -> A -> Prop))
  (empty': (B -> B -> Prop) -> (B -> B -> Prop))
  (measure : A -> Ord)
  (measure' : B -> Ord')
  (order_R : Ord -> Ord -> Prop)
  (order_R' : Ord' -> Ord' -> Prop)
  (compile : A -> B -> Prop)
  (eval : A -> A -> Prop)
  (eval': B -> B -> Prop) :=
    forall p q, compile p q ->
    ((forall p', eval p p' ->
    exists q', eval' q q' /\ compile p' q') \/
    (forall p', (empty eval) p p' /\ order_R (measure p') (measure p) ->
    compile p' q)) /\
    ((forall q', eval' q q' ->
    exists p', eval p p' /\ compile p' q') \/
    (forall q', (empty' eval') q q' /\ order_R' (measure' q') (measure' q) ->
    compile p q')).

End Simulation.
