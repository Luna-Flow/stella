# stella

This manual documents the intended `v0.2.0` release of `Luna-Flow/stella`, the current `main` branch.

## Overview

stella is a proof assistant written in MoonBit and still a work in progress. Its kernel is the `elab` package: the core syntax of a Martin-Löf type theory, evaluation into values, read-back into normal forms, and a bidirectional type checker whose definitional equality is decided by normalisation by evaluation.

The type theory has the unit type, $\Pi$ types, $\Sigma$ types, identity types with the $J$ eliminator, W types with recursion, and a cumulative hierarchy of predicative universes, with subtyping that is contravariant in the domain of $\Pi$ types.

The release candidate centers on these changes:

- The kernel types derive `Debug` instead of `Show`: print them with `debug_inspect`, `Repr(x)` or `@debug.to_string(x)`.
- The $J$ eliminator checks the domains of its motive, and `WRec` checks the domains of its family and motive by subtyping.
- `Rfl` compares its endpoints by conversion with $\eta$, `def_eq` is reflexive on neutral applications, and a stuck `wrec` reads back to a term that evaluates to itself.

## Install

```bash
moon add Luna-Flow/stella@0.2.0
```

Then import `"Luna-Flow/stella/elab"` and `"moonbitlang/core/list"`, which provides contexts and environments, in your `moon.pkg`. The package needs the MoonBit toolchain 0.10 or later (`moonc` ≥ 0.10) and has no dependencies besides the MoonBit core library.

> [!NOTE]
> `moon.mod` still declares `0.1.2`, the last published version. That version implements `Show` for the kernel types and lacks the fixes listed in the [changelog](../../CHANGELOG.md); the pages below describe `main`.

## Pages

The repository is one MoonBit package, `src/elab`, documented as `elab`. The treatise is a separate attachment.

| Part | Tutorial | API | Design |
| --- | --- | --- | --- |
| `elab`: syntax, evaluation, read-back, type checking | [tutorial](tutorial/elab.md) | [API](api/elab.md) | [design](design/elab.md) |
| Theory: from the untyped lambda calculus to Martin-Löf type theory | [treatise](../attachments/stella_foundations.typ) | | |

## Exported types

- Syntax: `TermInf` (inferable terms), `TermChk` (checkable terms), `Name`
- Semantics: `Value` (alias `Type`), `Neutral`
- State of the checker: `Context`, `Env`
- Errors: `TypeError`

## Exported functions

- Evaluation: `eval_inf`, `eval_chk`
- Semantic eliminations: `val_var`, `val_app`, `val_fst`, `val_snd`, `val_j_elim`, `val_w_rec`, `val_max_univ`
- Read-back: `quote`, `neutral_quote`
- Type checking: `type_inf`, `type_chk`, `type_inf_0`, `def_eq`

## Where to read next

The [tutorial](tutorial/elab.md) builds the identity function, pairs, a proof by path induction and a W-type recursion as MoonBit values. The [API](api/elab.md) states the contract of every function, including when it raises `TypeError` and when it panics, and the [design](design/elab.md) gives the typing rules and the theory of normalisation by evaluation.

- New to dependent types: read the treatise up to the chapter on the $\lambda\Pi$ calculus, then work through the [tutorial](tutorial/elab.md).
- Using the kernel in a library: keep the [API](api/elab.md) at hand; it says which arguments each function trusts.
- Contributing: read the [design](design/elab.md) before changing the kernel; it gives every typing rule in inference-rule notation, the invariants the checker relies on and the known gaps.

## Validation

Recommended release checks:

```bash
moon check --target all
moon test
```
