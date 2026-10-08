# elab API

The `elab` package (`src/elab`, import path `Luna-Flow/stella/elab`) is the kernel of stella: the syntax of a dependent type theory, its evaluation into values, the read-back of values into normal forms, and a bidirectional type checker. Its interface file is [`src/elab/pkg.generated.mbti`](../../../src/elab/pkg.generated.mbti).

Terms use de Bruijn indices: `Bound(0)` is the variable bound by the nearest enclosing binder. The binders are `Lam`, the second argument of `Pi`, `Sigma` and `W`, and nothing else. The [design notes](../design/elab.md) give the typing rules in full.

The examples on this page are tests in a package with this `moon.pkg`:

```text
import {
  "Luna-Flow/stella/elab",
  "moonbitlang/core/list",
}
```

and they bring the types into scope with:

```moonbit
using @elab {type TermChk, type TermInf, type Value}
```

## Syntax

### `Name`

`Name` identifies a free variable.

```mbti
pub(all) enum Name {
  Global(String)
  Local(Int)
  Quote(Int)
} derive(Eq, @debug.Debug)
pub fn Name::equal(Self, Self) -> Bool
```

| Constructor | Meaning |
| --- | --- |
| `Global(name)` | A constant declared by the user in the typing context, such as a postulated type `A`. |
| `Local(level)` | A variable that the type checker introduces when it goes under a binder; `level` counts the binders from the outside, starting at 0. |
| `Quote(level)` | A variable that `quote` introduces when it reads back a function body; `quote` turns it back into a `Bound` index. |

User code normally creates only `Global` names. `Name::equal` is the promoted `Eq` method; prefer `==`.

### `TermInf`

`TermInf` is the type of terms whose type the checker can infer.

```mbti
pub(all) enum TermInf {
  Bound(Int)
  Free(Name)
  UnitType
  Universe(Int)
  Ann(TermChk, TermChk)
  Pi(TermChk, TermChk)
  App(TermInf, TermChk)
  Sigma(TermChk, TermChk)
  Fst(TermInf)
  Snd(TermInf)
  Id(TermChk, TermChk, TermChk)
  JElim(TermChk, TermChk, TermChk, TermChk, TermChk, TermInf)
  W(TermChk, TermChk)
  WRec(TermChk, TermChk, TermChk, TermChk, TermInf)
} derive(Eq, @debug.Debug)
pub fn TermInf::equal(Self, Self) -> Bool
```

| Constructor | Notation | Meaning |
| --- | --- | --- |
| `Bound(i)` | $\#i$ | The variable bound by the $i$-th enclosing binder, counting from 0. |
| `Free(x)` | $x$ | A free variable, looked up in the typing context. |
| `UnitType` | $\mathbf 1$ | The unit type. |
| `Universe(i)` | $\mathcal U_i$ | The universe at level $i \ge 0$. |
| `Ann(t, T)` | $(t : T)$ | The checkable term `t` annotated with the type `T`. |
| `Pi(A, B)` | $\Pi_{x : A} B$ | Dependent function type; `B` is under one binder. |
| `App(f, t)` | $f\,t$ | Function application. |
| `Sigma(A, B)` | $\Sigma_{x : A} B$ | Dependent pair type; `B` is under one binder. |
| `Fst(p)`, `Snd(p)` | $\pi_1\,p$, $\pi_2\,p$ | Projections of a pair. |
| `Id(A, x, y)` | $\mathrm{Id}_A(x, y)$ | Identity type. |
| `JElim(A, x, P, d, y, p)` | $J$ | The based path eliminator: from `d : P x (refl x)` and `p : Id(A, x, y)`, a term of `P y p`. `P` is a function term of type $\Pi_{y : A} \mathrm{Id}_A(x, y) \to \mathcal U_k$. |
| `W(A, B)` | $W_{x : A} B$ | Well-founded tree type; `B` is under one binder. |
| `WRec(A, B, P, s, w)` | $\mathrm{wrec}$ | Recursion on `w : W(A, B)` into the motive `P`. Unlike in `W`, `B` here is a function term of type $A \to \mathcal U_k$. |

`TermInf::equal` compares terms structurally, which is $\alpha$-equivalence because variables are de Bruijn indices; prefer `==`.

### `TermChk`

`TermChk` is the type of terms that the checker checks against a known type.

```mbti
pub(all) enum TermChk {
  Inf(TermInf)
  UnitElement
  Lam(TermChk)
  Pair(TermChk, TermChk)
  Rfl(TermChk)
  Sup(TermChk, TermChk)
} derive(Eq, @debug.Debug)
pub fn TermChk::equal(Self, Self) -> Bool
```

| Constructor | Notation | Meaning |
| --- | --- | --- |
| `Inf(e)` | $e$ | An inferable term used where a checkable one is expected. |
| `UnitElement` | $\star$ | The element of the unit type. |
| `Lam(t)` | $\lambda.\,t$ | Function abstraction; `t` is under one binder. The domain is not written, it comes from the expected type. |
| `Pair(t, u)` | $(t, u)$ | Dependent pair. |
| `Rfl(t)` | $\mathrm{refl}\,t$ | Reflexivity proof of $\mathrm{Id}_A(t, t)$. |
| `Sup(a, f)` | $\sup(a, f)$ | Node of a W type with label `a` and child function `f`. |

A type is written as a `TermChk`, but most typing rules infer the type of a type, so a type position must contain `Inf(...)`, for example `Inf(UnitType)`.

```moonbit
test "syntax" {
  // the identity on the unit type, (λx. x) : 1 → 1
  let id_unit = TermInf::Ann(Lam(Inf(Bound(0))), Inf(Pi(Inf(UnitType), Inf(UnitType))))
  assert_true(id_unit == Ann(Lam(Inf(Bound(0))), Inf(Pi(Inf(UnitType), Inf(UnitType)))))
  debug_inspect(
    id_unit,
    content="Ann(Lam(Inf(Bound(0))), Inf(Pi(Inf(UnitType), Inf(UnitType))))",
  )
}
```

## Values

### `Value`

`Value` is the semantic domain: terms evaluated to weak head normal form, with binders represented as MoonBit functions.

```mbti
#alias(Type)
pub(all) enum Value {
  VNeutral(Neutral)
  VUnitType
  VUnitElement
  VUniverse(Int)
  VLam((Value) -> Value)
  VPi(Value, (Value) -> Value)
  VSigma(Value, (Value) -> Value)
  VPair(Value, Value)
  VId(Value, Value, Value)
  VRfl(Value)
  VW(Value, (Value) -> Value)
  VSup(Value, (Value) -> Value)
} derive(@debug.Debug)
```

Each constructor corresponds to a term constructor. A binder body becomes a function `(Value) -> Value`: `VPi(a, b)` is $\Pi_{x : a} b(x)$, and `VLam(f)` is the function $x \mapsto f(x)$. Values are also used as types, and `Type` is an alias of `Value` that the package uses for that role. Because values contain functions, `Value` has no `Eq`; compare values with `def_eq` or by comparing their normal forms from `quote`. `Debug` prints a function as `<function: ...>`.

### `Neutral`

`Neutral` is a computation that is stuck on a free variable.

```mbti
pub(all) enum Neutral {
  NFree(Name)
  NApp(Neutral, Value)
  NFst(Neutral)
  NSnd(Neutral)
  NJElim(Value, Value, Value, Value, Value, Neutral)
  NWRec(Value, (Value) -> Value, Value, Value, Neutral)
} derive(@debug.Debug)
```

A neutral term is a free variable followed by a spine of eliminations that cannot reduce: an application of a variable, a projection of a variable, or `J` or `wrec` on a variable. A neutral term is a value through `VNeutral`.

### `Context`, `Env`

`Context` assigns types to free variables; `Env` assigns values to bound variables.

```mbti
pub type Context = @list.List[(Name, Value)]
pub type Env = @list.List[Value]
```

A `Context` is searched from the head, so a later declaration shadows an earlier one. In an `Env`, the head is the value of `Bound(0)`, the next element the value of `Bound(1)`, and so on.

## Evaluation

### `eval_inf`, `eval_chk`

`eval_inf` and `eval_chk` evaluate a term in an environment.

```mbti
pub fn eval_inf(TermInf, @list.List[Value]) -> Value
pub fn eval_chk(TermChk, @list.List[Value]) -> Value
```

They compute the weak head normal form, $\llbracket t \rrbracket_\rho$ in the design notes: annotations are erased, binders become closures over the environment, and eliminations reduce through the `val_` functions below. Evaluation does not type-check. On an ill-typed term it can panic, for example when a non-function is applied or `Bound(i)` has no entry in the environment.

```moonbit
test "evaluate" {
  let id_unit = TermInf::Ann(Lam(Inf(Bound(0))), Inf(Pi(Inf(UnitType), Inf(UnitType))))
  let v = @elab.eval_inf(App(id_unit, UnitElement), @list.empty())
  debug_inspect(v, content="VUnitElement")
}
```

### `val_var`

`val_var` is the value of a free variable.

```mbti
pub fn val_var(Name) -> Value
```

`val_var(x)` is `VNeutral(NFree(x))`.

### `val_app`, `val_fst`, `val_snd`

These apply a function value and project a pair value.

```mbti
pub fn val_app(Value, Value) -> Value
pub fn val_fst(Value) -> Value
pub fn val_snd(Value) -> Value
```

They implement the $\beta$-rules $(\lambda f)\,v = f(v)$, $\pi_1 (v, w) = v$ and $\pi_2 (v, w) = w$. On a neutral argument they extend the neutral spine. On any other value they panic.

### `val_j_elim`

`val_j_elim` evaluates the path eliminator.

```mbti
pub fn val_j_elim(Value, Value, Value, Value, Value, Value) -> Value
```

`val_j_elim(a, x, p, d, y, e)` returns `d` when `e` is `VRfl(_)`, the rule $J(A, x, P, d, x, \mathrm{refl}\,x) = d$, extends the neutral spine when `e` is neutral, and panics otherwise.

### `val_w_rec`

`val_w_rec` evaluates W recursion.

```mbti
pub fn val_w_rec(Value, (Value) -> Value, Value, Value, Value) -> Value
```

`val_w_rec(a, b, p, s, w)` computes, for `w = VSup(l, f)`,

$$
\mathrm{wrec}(\sup(l, f)) = s\; l\; (\lambda z.\, f\,z)\; \bigl(\lambda z.\, \mathrm{wrec}(f\,z)\bigr),
$$

that is, the step function applied to the label, the children and the recursive results on the children. It extends the neutral spine when `w` is neutral and panics otherwise.

### `val_max_univ`

`val_max_univ` returns the larger of two universes.

```mbti
pub fn val_max_univ(Value, Value) -> Value
```

`val_max_univ(VUniverse(i), VUniverse(j))` is `VUniverse(max(i, j))`. Any other argument panics. The checker computes the level of a $\Pi$, $\Sigma$ or $W$ type with this rule but does not call the function.

## Normal forms

### `quote`, `neutral_quote`

`quote` reads a value back into a term in normal form; `neutral_quote` does the same for a neutral term.

```mbti
pub fn quote(Int, Value) -> TermChk
pub fn neutral_quote(Int, Neutral) -> TermInf
```

`quote(l, v)` expects `l` to be the number of binders the value is under, normally `0`. To read back a closure it applies the closure to a fresh variable `Quote(l)` and quotes the body at `l + 1`. `neutral_quote` turns a variable `Quote(k)` into the index `Bound(l - k - 1)` and leaves other names as `Free(x)`. The normal form of a term $t$ is `quote(0, eval_chk(t, @list.empty()))`; two terms with equal normal forms are $\beta$-equal.

```moonbit
test "normalise under a binder" {
  let id_unit = TermInf::Ann(Lam(Inf(Bound(0))), Inf(Pi(Inf(UnitType), Inf(UnitType))))
  // λy. (λx. x) y  normalises to  λy. y
  let t = TermChk::Lam(Inf(App(id_unit, Inf(Bound(0)))))
  debug_inspect(@elab.quote(0, @elab.eval_chk(t, @list.empty())), content="Lam(Inf(Bound(0)))")
}
```

## Type checking

### `TypeError`

`TypeError` is the error raised by the type checker.

```mbti
pub suberror TypeError {
  TypeError(String)
}
```

The message names the rule that failed, for example `Illegal Application`, `Expected Pi type for Lambda`, `Type Mismatch: inferred type is not a subtype of expected type`, `Rfl endpoints mismatch` or `Unknown Identifier: Global("b")`.

### `type_inf`, `type_chk`

`type_inf` infers the type of a term; `type_chk` checks a term against a type.

```mbti
pub fn type_inf(Int, @list.List[(Name, Value)], @list.List[Value], TermInf) -> Value raise TypeError
pub fn type_chk(Int, @list.List[(Name, Value)], @list.List[Value], TermChk, Value) -> Unit raise TypeError
```

`type_inf(l, ctx, env, e)` returns the type of `e` as a value, and `type_chk(l, ctx, env, t, ty)` returns normally when `t` has type `ty`; both raise `TypeError` otherwise. The arguments describe the position of the term:

- `l` is the number of binders the checker has entered, and `Local(l)` is the next fresh variable;
- `ctx` contains the user's `Global` declarations and one entry `(Local(k), A_k)` for every binder entered;
- `env` has one entry `val_var(Local(k))` for every binder entered, the innermost first.

At the top level, pass `0`, the user's context and an empty environment. `Bound(i)` is resolved through `env` and then `ctx`, so `env` may contain only variables that are declared in `ctx`; any other value raises an internal error. In checking mode, a term that can only be inferred is accepted when its inferred type is a subtype of the expected one (cumulativity, see `def_eq`).

```moonbit
test "check and infer" {
  let poly_id_ty = TermChk::Inf(Pi(Inf(Universe(0)), Inf(Pi(Inf(Bound(0)), Inf(Bound(1))))))
  let poly_id = TermInf::Ann(Lam(Lam(Inf(Bound(0)))), poly_id_ty)
  let ty = @elab.type_inf(0, @list.empty(), @list.empty(), poly_id)
  debug_inspect(@elab.quote(0, ty), content="Inf(Pi(Inf(Universe(0)), Inf(Pi(Inf(Bound(0)), Inf(Bound(1))))))")
  @elab.type_chk(0, @list.empty(), @list.empty(), Inf(UnitType), VUniverse(1))
}
```

### `type_inf_0`

`type_inf_0` infers the type of a closed term in a context of global declarations.

```mbti
pub fn type_inf_0(@list.List[(Name, Value)], TermInf) -> Value raise TypeError
```

`type_inf_0(ctx, e)` is `type_inf(0, ctx, @list.empty(), e)`. Declare a constant by adding `(Global(name), type)` to `ctx`; the type is a value, for example `VUniverse(0)` for a type variable or `VNeutral(NFree(Global("A")))` for an element of a declared type `A`.

```moonbit
test "global declarations" {
  let ctx : @elab.Context = @list.List([
    (Global("a"), VNeutral(NFree(Global("A")))),
    (Global("A"), VUniverse(0)),
  ])
  let ty = @elab.type_inf_0(ctx, Free(Global("a")))
  debug_inspect(@elab.quote(0, ty), content="Inf(Free(Global(\"A\")))")
  let err = try @elab.type_inf_0(ctx, App(Free(Global("a")), UnitElement)) |> ignore catch {
    TypeError(msg) => msg
  } noraise {
    _ => "no error"
  }
  inspect(err, content="Illegal Application")
}
```

### `def_eq`

`def_eq` decides whether one type is a subtype of another in the empty context.

```mbti
pub fn def_eq(Int, Value, Value) -> Bool
```

`def_eq(l, s, t)` returns `true` when $s \le t$ under the cumulative subtyping of the design notes: $\mathcal U_i \le \mathcal U_j$ for $i \le j$, $\Pi$ types are contravariant in the domain and covariant in the codomain, $\Sigma$ types are invariant in the first component and covariant in the second, and all other types are compared by conversion. Despite its name the relation is not symmetric: `def_eq(0, VUniverse(0), VUniverse(1))` is `true` and `def_eq(0, VUniverse(1), VUniverse(0))` is `false`.

> [!NOTE]
> Because the context is empty, `def_eq` cannot look up the type of a free variable. Two neutral terms are then compared by their read-backs, so `f x` equals `f x` for a free `f`, but arguments that are only $\eta$-equal, such as `f g` and `f (λx. g x)`, are not identified. Inside `type_chk`, where the context is known, $\eta$ is used.

```moonbit
test "cumulativity" {
  assert_true(@elab.def_eq(0, VUniverse(0), VUniverse(1)))
  assert_false(@elab.def_eq(0, VUniverse(1), VUniverse(0)))
  let narrow = Value::VPi(VUniverse(0), _ => VUniverse(0))
  let wide = Value::VPi(VUniverse(1), _ => VUniverse(0))
  assert_true(@elab.def_eq(0, wide, narrow))
}
```

## Deprecated

The promoted methods below are kept for source compatibility. They are hidden from the interface file and warn when called from another package.

| Method | Replacement |
| --- | --- |
| `Name::not_equal`, `TermChk::not_equal`, `TermInf::not_equal` | `a != b` |
| `Name::to_repr`, `TermChk::to_repr`, `TermInf::to_repr`, `Neutral::to_repr`, `Value::to_repr` | `Repr(x)`, `@debug.to_string(x)` or `debug_inspect(x)` |

Before the MoonBit 0.10 migration, `Name`, `TermChk`, `TermInf`, `Neutral` and `Value` implemented `Show`. These implementations were removed: `inspect(x)`, `x.to_string()` and `"\{x}"` no longer compile for these types. Use the `Debug` forms instead.
