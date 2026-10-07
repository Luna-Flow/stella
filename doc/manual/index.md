# stella

stella is a proof assistant written in MoonBit and still a work in progress. Its core is the `elab` package, a bidirectional type checker for Martin-Löf type theory based on normalization by evaluation.

The checker supports the unit type, Π types, Σ types, identity types with the J eliminator, W types and a universe hierarchy, with contravariant subtyping for Π types.

## Packages

- **`elab`** (`src/elab`): abstract syntax, evaluation, quotation and bidirectional type checking. See the [API reference](api/elab.md), the [design notes](design/elab.md) and the [tutorial](tutorial/elab.md).

## Theory

The treatise below develops the type theory behind stella, from the untyped lambda calculus to Martin-Löf type theory, and explains how the kernel elaborates it. Read it as the narrative overview before working on elaboration details or extending the proof language.

[Foundations and Elaboration of Stella Based on Dependent Type Theory](../attachments/stella_foundations.typ)
