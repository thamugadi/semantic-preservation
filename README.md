# semantic-preservation

## Update (06/02/2024)

The purpose of this repo is to give a minimal example (not that minimal, I finally realized lol) of a compiler for which the forward simulation property is verified.

I considered a brainfuck-like language, compiling to a kind of generic assembler; many aspects were difficult to handle, notably the fact that after compilation, I need to perform a linking operation a posteriori, to resolve the absolute addresses of the jumps.

The proof remains incomplete, but the skeleton is there. For the moment, I'm thinking of putting the project on hold, as it turned out to be much more difficult than I had imagined. This was my first real contact with Coq and dependent types, and it allowed me to make progress on the basics :)

## Introduction

- Main reference: https://xavierleroy.org/publi/compcert-backend.pdf
- This is an attempt to formalise the semantic conservation properties for compilers described in Xavier Leroy's paper.
- This repository will try to use them to formally verify a compiler, defined in [src/Compiler.v](src/Compiler.v), transforming expressions between 2 toy languages.

## Semantics

- We define small-step semantics for two basic languages: a source language and an assembly language for a virtual architecture: [src/Language.v](src/Language.v) and [src/Assembly.v](src/Assembly.v)
  
## Simulation property

- The aim of Leroy's paper is to describe how a source program S and a target program C retain the same semantics if the compilation process succeeds.
- Several relations are defined in his paper to express semantic preservation. In [src/Simulation.v](src/Simulation.v) are included the definitions to construct the lockstep, "plus", "option" and "star" simulation relations described in p. 16.

## Proof of 'plus' simulation

- The proof ([src/Verification.v](src/Verification.v)) is still incomplete.
- Vectors are used instead of lists, as some lemmas were easier to prove for vectors, like read\_instr\_eq
