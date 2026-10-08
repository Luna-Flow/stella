# STELLA

[![img](https://img.shields.io/badge/Maintainer-KCN--judu-violet)](https://github.com/KCN-judu) [![img](https://img.shields.io/badge/License-Apache%202.0-blue)](https://github.com/Luna-Flow/stella/blob/main/LICENSE) ![img](https://img.shields.io/badge/State-active-success)

stella is a proof assistant written in [MoonBit](https://www.moonbitlang.com/), still a work in progress. The `main` branch, to be released as 0.2.0, provides its kernel: a bidirectional type checker for Martin-Löf type theory based on normalisation by evaluation, with the unit type, $\Pi$, $\Sigma$, identity types with $J$, W types and a cumulative universe hierarchy.

## Installation

```bash
moon add Luna-Flow/stella@0.1.2
```

`moon.mod` still declares 0.1.2, the last published version; it implements `Show` for the kernel types, which `main` replaces with `Debug`.

```text
// moon.pkg
import {
  "Luna-Flow/stella/elab",
  "moonbitlang/core/list",
}
```

## Example

```moonbit
using @elab {type TermInf}

test {
  // (λx. x : 1 → 1) has type 1 → 1, and applied to ⋆ it computes ⋆
  let id_unit = TermInf::Ann(Lam(Inf(Bound(0))), Inf(Pi(Inf(UnitType), Inf(UnitType))))
  let ty = @elab.type_inf_0(@list.empty(), id_unit)
  debug_inspect(@elab.quote(0, ty), content="Inf(Pi(Inf(UnitType), Inf(UnitType)))")
  let v = @elab.eval_inf(App(id_unit, UnitElement), @list.empty())
  debug_inspect(@elab.quote(0, v), content="UnitElement")
}
```

## Packages

| Package | Contents |
| --- | --- |
| `Luna-Flow/stella/elab` | Core syntax, values, evaluation, read-back, bidirectional type checking |

## Features

- [x] Simply typed lambda calculus
- [x] Unit type
- [x] Π types
- [x] Σ types
- [x] Identity types and the J eliminator
- [x] W types
- [x] Universe hierarchy
- [x] Contravariant subtyping for Π types

## Requirements

MoonBit toolchain with `moonc` 0.10 or newer. No dependencies besides the MoonBit core library.

## Documentation

- Online manual (English, Chinese, Japanese): <https://lunaflow.cn/en/stella/>
- English source: [`doc/manual/index.md`](doc/manual/index.md), with the [API reference](doc/manual/api/elab.md), the [tutorial](doc/manual/tutorial/elab.md) (from the identity function to path induction and W-type recursion) and the [design notes](doc/manual/design/elab.md) (typing rules, normalisation by evaluation, known gaps).
- Changes between versions: [`CHANGELOG.md`](CHANGELOG.md).

## References

- [Towards a practical programming language based on dependent type theory](https://www.cse.chalmers.se/~ulfn/papers/thesis.pdf)
- [A tutorial implementation of a dependently typed lambda calculus](https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf)

## Contributing and contact

Read the [design notes](doc/manual/design/elab.md) before changing the kernel, and run `moon check --target all` and `moon test` before opening a pull request.

- [Chinese] Luna Flow QQ group: 762311556
- [English/Japanese/Chinese] Email: zhehao0827 at 163.com

## License

Apache-2.0. See [`LICENSE`](LICENSE).
