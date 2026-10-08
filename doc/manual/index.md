# stella

stella is a proof assistant written in MoonBit and still a work in progress. Its kernel is the `elab` package: the core syntax of a Martin-Löf type theory, evaluation into values, read-back into normal forms, and a bidirectional type checker whose definitional equality is decided by normalisation by evaluation.

The type theory has the unit type, $\Pi$ types, $\Sigma$ types, identity types with the $J$ eliminator, W types with recursion, and a cumulative hierarchy of predicative universes, with subtyping that is contravariant in the domain of $\Pi$ types.

## Packages

| Package | Contents | API | Tutorial | Design |
| --- | --- | --- | --- | --- |
| `elab` (`src/elab`) | Terms (`TermInf`, `TermChk`, `Name`), values (`Value`, `Neutral`), evaluation and read-back (`eval_inf`, `eval_chk`, `quote`), type checking (`type_inf`, `type_chk`, `type_inf_0`, `def_eq`, `TypeError`). | [API](api/elab.md) | [Tutorial](tutorial/elab.md) | [Design](design/elab.md) |

The package also contains white-box tests (`elaboration_wbtest.mbt`) for universe levels, subtyping and the typing of annotations.

## Reading paths

- **New to dependent types.** Read the treatise below up to the chapter on the $\lambda\Pi$ calculus, then work through the [tutorial](tutorial/elab.md), which builds the identity function, pairs and a proof by path induction as MoonBit values.
- **Using the kernel.** The [tutorial](tutorial/elab.md) shows how to declare constants, check terms and normalise them; the [API reference](api/elab.md) states the contract of every function, including when it raises `TypeError` and when it panics.
- **Working on the kernel.** The [design notes](design/elab.md) give every typing rule in inference-rule notation, the evaluation and read-back equations, the invariants the checker relies on, and the known gaps between the implementation and the theory.

## Toolchain and installation

stella requires MoonBit with `moonc` 0.10 or newer and has no dependencies besides the MoonBit core library.

```bash
moon add Luna-Flow/stella@0.1.2
```

```text
import {
  "Luna-Flow/stella/elab",
  "moonbitlang/core/list",
}
```

Run `moon check --target all` and `moon test` before opening a pull request.

## Theory

The treatise below develops the type theory behind stella, from the untyped lambda calculus to Martin-Löf type theory, and explains how the kernel elaborates it. Read it as the narrative overview before working on elaboration details or extending the proof language.

[Foundations and Elaboration of Stella Based on Dependent Type Theory](../attachments/stella_foundations.typ)
