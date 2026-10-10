# Changelog

All notable changes to this project are documented in this file.

## Unreleased

## 0.2.0 - 2026-10-10

### Breaking changes

- `Name`, `TermChk`, `TermInf`, `Neutral` and `Value` derive `Debug` instead of `Show`. Their `Show` implementations are removed, so `inspect(x)`, `x.to_string()` and `"\{x}"` no longer compile for these types. Use `debug_inspect(x)`, `@debug.to_string(x)` or `"\{Repr(x)}"` instead.

### Fixed

- `JElim` now checks the domains of its motive: the motive's type must accept $A$ as its first argument and $\mathrm{Id}(A, x, y)$ as its second, up to subtyping. Before, only the shape $\Pi(\_, \Pi(\_, \mathcal U_k))$ was checked, so ill-typed motives were accepted or crashed the checker with `RuntimeError: unreachable` (#19). The check was lost when cumulative universes were introduced.
- `def_eq` is reflexive on neutral terms: when the type of a neutral head is unknown (as in `def_eq`, which has no context), `conv_neu` now compares the read-backs instead of returning `false`, so `def_eq(0, f tt, f tt)` is `true` (#18).
- `Rfl` compares its endpoints by type-directed conversion, so `refl f : Id(1 → 1, f, λx. f x)` and `refl tt : Id(1, tt, u)` are accepted, as $\eta$ requires (#20).
- `quote` reads back the family `B` of a stuck `WRec` as a function term, so evaluating a read-back stuck `wrec` gives the same value instead of crashing (#21).
- `WRec` checks the domains of `B` and of the motive by subtyping instead of comparing read-backs, so definitionally equal domains are accepted.

### Changed

- Migrated to MoonBit 0.10 (`moonc` 0.10 or newer is required).
- The manifests moved from `moon.mod.json` and `moon.pkg.json` to the `moon.mod` and `moon.pkg` formats.
- Trait methods are promoted explicitly in `src/elab/extends.mbt`: `Name::equal`, `TermChk::equal` and `TermInf::equal` stay methods. `not_equal` and the `to_repr` methods are kept as deprecated, hidden methods; use `!=` and `Repr(x)` instead.
- `not(x)` was replaced by `!x`, and the tests use `try ... catch ... noraise` instead of the deprecated `try?`.

### Documentation

- Documentation rewritten (API, tutorial and design pages for `elab`, and the manual overview) with zh_CN and ja_JP translations. The design notes give the typing rules in inference-rule notation, the NbE equations and the known gaps of the kernel.
- The README describes the current version only.
- The manual follows the luna-generic layout: the overview gains install, pages, exported items, reading paths and validation sections; the API page gains purpose and importing sections and an example of the semantic eliminations; the tutorial gains a task table and a W-type recursion example; the design page gains a constraints section, a corrected substitution lemma for de Bruijn indices, and two known gaps (no $\eta$ below identity and W values, a panic on open terms at the top level).

## 0.1.2

- Bidirectional NbE type checker for Martin-Löf type theory with unit, Π, Σ, identity and W types, a cumulative universe hierarchy and Π subtyping.
