# Changelog

All notable changes to this project are documented in this file.

## Unreleased

### Breaking changes

- `Name`, `TermChk`, `TermInf`, `Neutral` and `Value` derive `Debug` instead of `Show`. Their `Show` implementations are removed, so `inspect(x)`, `x.to_string()` and `"\{x}"` no longer compile for these types. Use `debug_inspect(x)`, `@debug.to_string(x)` or `"\{Repr(x)}"` instead.

### Fixed

- `JElim` now checks the domains of its motive: the motive's type must accept $A$ as its first argument and $\mathrm{Id}(A, x, y)$ as its second, up to subtyping. Before, only the shape $\Pi(\_, \Pi(\_, \mathcal U_k))$ was checked, so ill-typed motives were accepted or crashed the checker with `RuntimeError: unreachable` (#19). The check was lost when cumulative universes were introduced.

### Changed

- Migrated to MoonBit 0.10 (`moonc` 0.10 or newer is required).
- The manifests moved from `moon.mod.json` and `moon.pkg.json` to the `moon.mod` and `moon.pkg` formats.
- Trait methods are promoted explicitly in `src/elab/extends.mbt`: `Name::equal`, `TermChk::equal` and `TermInf::equal` stay methods. `not_equal` and the `to_repr` methods are kept as deprecated, hidden methods; use `!=` and `Repr(x)` instead.
- `not(x)` was replaced by `!x`, and the tests use `try ... catch ... noraise` instead of the deprecated `try?`.

### Documentation

- Documentation rewritten (API, tutorial and design pages for `elab`, and the manual overview) with zh_CN and ja_JP translations. The design notes give the typing rules in inference-rule notation, the NbE equations and the known gaps of the kernel.
- The README describes the current version only.

## 0.1.2

- Bidirectional NbE type checker for Martin-Löf type theory with unit, Π, Σ, identity and W types, a cumulative universe hierarchy and Π subtyping.
