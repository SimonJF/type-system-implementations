# Type system implementation playground

## Overview

This project includes a few different implementations of typecheckers. It's
mainly as a tool for me to learn how to do gradually more interesting
typecheckers, and I will write blogs about these at some point.

In the meantime though, here are the ones I've implemented:

  * `stlc`: basic simply-typed lambda calculus, requiring an annotation on
      lambdas
  * `stlc_noann`: constraint-based STLC, allowing you to omit annotations on
      lambdas. Solves constraints at the end.
  * `stlc_noann_onthefly`: as above, but performs unification on the go rather
      than at the end.
  * `bidir`: basic bidirectional typechecker
  * `hindley_milner`: Hindley-Milner type inference
  * `cocontextual`: Co-contextual typing (type environments are an *output*
      rather than an input)
  * `cocontextual_linear`: A linear type system implemented simply by abstracting out and tweaking some parameters to the cocontextual type system
  * `linear_subtractive`: A subtractive linear type system where a variable is removed from its context as soon as it is used. (Leftover typing)
  * `linear_additive`: An additive linear type system where a variable is marked upon use; checks are made when combining usage maps and at binding sites

The REPL and Parser code is parameterised over the particular language
implementation. To implement a new typechecker, program against the interface in
`common/language_sig.ml` and then add the module to `bin/main.ml`.

## Usage
`./run.sh <name>`, where `name` is one of the supported typecheckers.
