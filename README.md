# semantic-preservation

Main reference: https://xavierleroy.org/publi/compcert-backend.pdf

- This is an attempt to formalise the semantic conservation properties for compilers described in Xavier Leroy's paper.
- (not done yet) this repository will try to use them to formally verify a compiler between transforming expressions between 2 toy languages: [src/Verification.v](src/Verification.v)

## Semantics

- It is assumed that the operational semantics of the two languages, target and source, have been formalised.
- In the example given in this repository, we will define small-step semantics for two basic languages: a source language and an assembly language for a virtual architecture: [src/Language.v](src/Language.v) and [src/Assembly.v](src/Assembly.v)
  
## Simulation property

- The aim of Leroy's paper is to describe how a source program S and a target program C retain the same semantics if the compilation process, (not done yet) defined in [src/Compiler.v](src/Compiler.v), succeeds. 
- Several relations are defined in his paper to express semantic preservation. In [src/Simulation.v](src/Simulation.v) are included the definitions to construct the lockstep, "plus", "option" and "star" simulation relations described in p. 16.
