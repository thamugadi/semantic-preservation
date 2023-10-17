# semantic-preservation

- Main reference: https://xavierleroy.org/publi/compcert-backend.pdf
- This is an attempt to formalise the semantic conservation properties for compilers described in Xavier Leroy's paper.
- This repository will try to use them to formally verify a compiler, defined in [src/Compiler.v](src/Compiler.v) between transforming expressions between 2 toy languages: [src/Verification.v](src/Verification.v)

## Semantics

- It is assumed that the operational semantics of the two languages, target and source, have been formalised.
- In the example given in this repository, we will define small-step semantics for two basic languages: a source language and an assembly language for a virtual architecture: [src/Language.v](src/Language.v) and [src/Assembly.v](src/Assembly.v)
  
## Simulation property

- The aim of Leroy's paper is to describe how a source program S and a target program C retain the same semantics if the compilation process succeeds.
- Several relations are defined in his paper to express semantic preservation. In [src/Simulation.v](src/Simulation.v) are included the definitions to construct the lockstep, "plus", "option" and "star" simulation relations described in p. 16.

## Proof of 'plus' simulation

- The proof ([src/Verification.v](src/Verification.v)) is still incomplete.
- Lemmas with sufficient conditions for eval'+ to hold between two target states would be helpful.
