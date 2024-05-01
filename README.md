# semantic-preservation
## Introduction

The purpose of this repo is to give a minimal example of a compiler for which the forward simulation property is verified. The proof is located in [src/Verification.v](src/Verification.v).

I considered an abstract machine using absolute addresses for ``Jump`` as a target, and one using a BF-like ``Jump`` / ``Ret``, both jumping one instruction after the associated instruction, as a source. The small compiler used is defined in [src/Compiler.v](src/Compiler.v).

The proof of some lemmas is still missing, and those are admitted for the moment. This was my first real contact with Coq and dependent types, and it allowed me to make progress on the basics. Also, it makes extensive use of CoqHammer, which makes some proofs quite incomprehensible.

The ``first_attempt`` folder contains previous attempts to prove the property, in particular through an approach using vectors, in the belief that this would simplify the proof of certain lemmas. This was quite true, but it made it too complex to state certain theorems, and I preferred to give up on it.

It is globally a matter of proving that given two source states p and p' and a target state q, if

- p compiles into q
- p evaluates into p'

then there exist q' such as:

- p' compiles into q'
- q evaluates+ into q'

where "+" is the transitive closure.

Main reference: https://xavierleroy.org/publi/compcert-backend.pdf

## Semantics

- Small-step semantics for the two abstract machines are defined in [src/Language.v](src/Language.v) and [src/Assembly.v](src/Assembly.v)
  
## Simulation property

- The aim of [Leroy's paper](https://xavierleroy.org/publi/compcert-backend.pdf) is to describe how a source program S and a target program C retain the same semantics if the compilation process succeeds.
- Several relations are defined to express semantic preservation. In [src/Simulation.v](src/Simulation.v) are included the definitions to construct the lockstep, "plus", "option" and "star" simulation relations described in p. 16.
