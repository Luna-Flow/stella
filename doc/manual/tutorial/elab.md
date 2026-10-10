# elab tutorial

This tutorial shows you how to write terms of stella's type theory as MoonBit values, ask the kernel for their types, check them against types you give, and compute their normal forms. It starts with the identity function and ends with a proof by path induction and a recursion on a W type. The typing rules behind each step are in the [design notes](../design/elab.md).

| I want to | Use |
| --- | --- |
| write a term | the constructors of `TermInf` and `TermChk`, with `Bound(i)` for variables |
| infer the type of a closed term | `type_inf_0(ctx, e)` |
| check a term against a type | `type_chk(0, ctx, @list.empty(), t, ty)` |
| postulate a constant | a `(Global(name), type)` entry in the `Context` |
| compute a normal form | `quote(0, eval_chk(t, @list.empty()))` |
| compare two types | `def_eq(0, s, t)`, which tests $s \le t$ |
| print a term or value | `debug_inspect`, `Repr(x)` or `@debug.to_string(x)` |

## Quick start

Add the module to your project:

```bash
moon add Luna-Flow/stella@0.2.0
```

Import the package and the list package, which provides contexts and environments, in your `moon.pkg`:

```moonbit nocheck
import {
  "Luna-Flow/stella/elab",
  "moonbitlang/core/list",
}
```

The smallest useful program type-checks the identity function on the unit type and applies it:

```moonbit
using @elab {type TermChk, type TermInf, type Value}

test "quick start" {
  // (λx. x : 1 → 1)
  let id_unit = TermInf::Ann(Lam(Inf(Bound(0))), Inf(Pi(Inf(UnitType), Inf(UnitType))))
  let ty = @elab.type_inf_0(@list.empty(), id_unit)
  debug_inspect(@elab.quote(0, ty), content="Inf(Pi(Inf(UnitType), Inf(UnitType)))")
  let v = @elab.eval_inf(App(id_unit, UnitElement), @list.empty())
  debug_inspect(@elab.quote(0, v), content="UnitElement")
}
```

Three ideas appear here. A function `Lam` has no domain annotation, so the kernel cannot infer its type; `Ann` supplies the type. `type_inf_0` returns the type as a *value*, and `quote(0, _)` turns a value back into a term you can print. `eval_inf` computes, and the application reduces to `UnitElement`.

## Everyday tasks

### Read and write de Bruijn indices

Variables are numbers: `Bound(0)` is the variable of the nearest enclosing binder, `Bound(1)` the one outside it, and so on. The binders are `Lam` and the second argument of `Pi`, `Sigma` and `W`. The polymorphic identity $\lambda A.\,\lambda x.\,x : \Pi_{A : \mathcal U_0} \Pi_{x : A} A$ is written like this:

```moonbit
fn poly_id() -> TermInf {
  // Π(A : U0). Π(x : A). A  — inside the inner Π, A is Bound(1)
  let ty = TermChk::Inf(Pi(Inf(Universe(0)), Inf(Pi(Inf(Bound(0)), Inf(Bound(1))))))
  Ann(Lam(Lam(Inf(Bound(0)))), ty)
}

test "polymorphic identity" {
  let ty = @elab.type_inf_0(@list.empty(), poly_id())
  debug_inspect(
    @elab.quote(0, ty),
    content="Inf(Pi(Inf(Universe(0)), Inf(Pi(Inf(Bound(0)), Inf(Bound(1))))))",
  )
  // instantiate A := 1 and apply to ⋆
  let app = TermInf::App(App(poly_id(), Inf(UnitType)), UnitElement)
  debug_inspect(@elab.quote(0, @elab.type_inf_0(@list.empty(), app)), content="Inf(UnitType)")
  debug_inspect(@elab.quote(0, @elab.eval_inf(app, @list.empty())), content="UnitElement")
}
```

In the type, the domain of the inner $\Pi$ is `Bound(0)`, the $A$ bound by the outer $\Pi$; its codomain is under one more binder, so the same $A$ is `Bound(1)` there. The type of the application is computed by substituting: the kernel applies the codomain closure to the argument's value.

### Declare constants in a context

A context lists the types of free variables named `Global(...)`. Use it to postulate a type and an element of it:

```moonbit
fn ctx_a() -> @elab.Context {
  // A : U0, a : A   (the head of the list is searched first)
  @list.List([(Global("a"), VNeutral(NFree(Global("A")))), (Global("A"), VUniverse(0))])
}

test "constants" {
  let ty = @elab.type_inf_0(ctx_a(), Free(Global("a")))
  debug_inspect(@elab.quote(0, ty), content="Inf(Free(Global(\"A\")))")
}
```

The type of `a` is the value of the term `A`, which is the neutral variable `VNeutral(NFree(Global("A")))`.

### Work with pairs

A pair is checked against a $\Sigma$ type, and the projections infer their types from it:

```moonbit
test "pairs" {
  let ty_a = TermChk::Inf(Free(Global("A")))
  let a = TermChk::Inf(Free(Global("a")))
  // (a, ⋆) : Σ(x : A). 1
  let pair = TermInf::Ann(Pair(a, UnitElement), Inf(Sigma(ty_a, Inf(UnitType))))
  debug_inspect(@elab.quote(0, @elab.type_inf_0(ctx_a(), Fst(pair))), content="Inf(Free(Global(\"A\")))")
  debug_inspect(@elab.quote(0, @elab.type_inf_0(ctx_a(), Snd(pair))), content="Inf(UnitType)")
  debug_inspect(@elab.quote(0, @elab.eval_inf(Fst(pair), @list.empty())), content="Inf(Free(Global(\"a\")))")
}
```

### Handle type errors

The checker raises `TypeError` with a message that names the failed rule. Catch it like any MoonBit error:

```moonbit
fn infer_or_message(ctx : @elab.Context, e : TermInf) -> String {
  try @elab.type_inf_0(ctx, e) catch {
    TypeError(msg) => msg
  } noraise {
    ty => "type: \{Repr(@elab.quote(0, ty))}"
  }
}

test "errors" {
  inspect(infer_or_message(ctx_a(), App(Free(Global("a")), UnitElement)), content="Illegal Application")
  inspect(infer_or_message(ctx_a(), Free(Global("b"))), content="Unknown Identifier: Global(\"b\")")
  inspect(infer_or_message(ctx_a(), Universe(0)), content="type: Inf(Universe(1))")
}
```

### Use universes and cumulativity

`Universe(i)` has type `Universe(i + 1)`, and a type in $\mathcal U_i$ is also accepted in every larger universe:

```moonbit
test "universes" {
  debug_inspect(@elab.type_inf_0(@list.empty(), Universe(0)), content="VUniverse(1)")
  // 1 : U0, and therefore also 1 : U1
  @elab.type_chk(0, @list.empty(), @list.empty(), Inf(UnitType), VUniverse(1))
  // a function type lives in the larger universe of its parts
  debug_inspect(
    @elab.type_inf_0(@list.empty(), Pi(Inf(UnitType), Inf(Universe(0)))),
    content="VUniverse(1)",
  )
  assert_true(@elab.def_eq(0, VUniverse(0), VUniverse(1)))
  assert_false(@elab.def_eq(0, VUniverse(1), VUniverse(0)))
}
```

`def_eq` is the subtyping test used by the checker, not a symmetric equality.

## Going further

### Prove something by path induction

The eliminator `JElim(A, x, P, d, y, p)` turns a proof `d` of `P x (refl x)` and a path `p : Id(A, x, y)` into a proof of `P y p`. The motive `P` must be an inferable function, so annotate it. Here the motive is constant, $P = \lambda y.\,\lambda p.\,A$, and $J$ transports `a` along `refl a`:

```moonbit
test "path induction" {
  let ty_a = TermChk::Inf(Free(Global("A")))
  let a = TermChk::Inf(Free(Global("a")))
  // P : Π(y : A). Id(A, a, y) → U0, P = λy. λp. A
  let motive_ty = TermChk::Inf(
    Pi(ty_a, Inf(Pi(Inf(Id(ty_a, a, Inf(Bound(0)))), Inf(Universe(0))))),
  )
  let motive = TermChk::Inf(Ann(Lam(Lam(ty_a)), motive_ty))
  let path = TermInf::Ann(Rfl(a), Inf(Id(ty_a, a, a)))
  let j = TermInf::JElim(ty_a, a, motive, a, a, path)
  debug_inspect(@elab.quote(0, @elab.type_inf_0(ctx_a(), j)), content="Inf(Free(Global(\"A\")))")
  // J computes on refl: J(A, a, P, d, a, refl a) = d
  debug_inspect(@elab.quote(0, @elab.eval_inf(j, @list.empty())), content="Inf(Free(Global(\"a\")))")
}
```

### Recurse on a W type

A W type $W_{x : A} B(x)$ is the type of well-founded trees whose nodes carry a label $a : A$ and have one child for each element of $B(a)$. `Sup(a, f)` builds a node from a label and a child function, and `WRec(A, B, P, s, w)` computes by recursion on `w`. Postulate a label type `A`, a family `B`, a label `a`, a child function `kids` and a tree `w` to work with:

```moonbit
fn tree_ctx() -> @elab.Context {
  // A : U0, B : A → U0, a : A, kids : B a → W(x : A). B x, w : W(x : A). B x
  let ty_a = @elab.val_var(Global("A"))
  let fam = @elab.val_var(Global("B"))
  let tree = Value::VW(ty_a, x => @elab.val_app(fam, x))
  @list.List([
    (Global("w"), tree),
    (Global("kids"), VPi(@elab.val_app(fam, @elab.val_var(Global("a"))), _ => tree)),
    (Global("a"), ty_a),
    (Global("B"), VPi(ty_a, _ => VUniverse(0))),
    (Global("A"), VUniverse(0)),
  ])
}

test "W recursion" {
  let ty_a = TermChk::Inf(Free(Global("A")))
  let fam = TermChk::Inf(Free(Global("B")))
  // W(x : A). B x  — the family is a body under one binder
  let tree = TermChk::Inf(W(ty_a, Inf(App(Free(Global("B")), Inf(Bound(0))))))
  // P = λt. A : W(x : A). B x → U0
  let motive = TermChk::Inf(Ann(Lam(ty_a), Inf(Pi(tree, Inf(Universe(0))))))
  // s = λl. λf. λh. l  returns the label of the root
  let step = TermChk::Lam(Lam(Lam(Inf(Bound(2)))))
  let node = TermInf::Ann(Sup(Inf(Free(Global("a"))), Inf(Free(Global("kids")))), tree)
  let root = TermInf::WRec(ty_a, fam, motive, step, node)
  debug_inspect(@elab.quote(0, @elab.type_inf_0(tree_ctx(), root)), content="Inf(Free(Global(\"A\")))")
  // wrec computes on sup: s a kids (λb. wrec(kids b)) = a
  debug_inspect(@elab.quote(0, @elab.eval_inf(root, @list.empty())), content="Inf(Free(Global(\"a\")))")
  // on a variable tree it is stuck, and reads back as a WRec term
  let stuck = TermInf::WRec(ty_a, fam, motive, step, Free(Global("w")))
  assert_true(@elab.quote(0, @elab.eval_inf(stuck, @list.empty())) is Inf(WRec(_, _, _, _, Free(Global("w")))))
}
```

The step function receives the label `l`, the child function `f` and the recursive results `h`, one for each child; its type is $\Pi_{l : A} \Pi_{f : B(l) \to W} \Pi_{h : \Pi_{b : B(l)} P(f\,b)}\, P(\sup(l, f))$. In `WRec`, `B` is an inferable function term, here the constant `B` itself, while in `W` it is a body under a binder.

### Normalise terms and compare them

The normal form of a term is the read-back of its value. Normalisation reduces under binders, so it decides $\beta$-equality of terms:

```moonbit
fn normal_form(t : TermChk) -> TermChk {
  @elab.quote(0, @elab.eval_chk(t, @list.empty()))
}

test "normal forms" {
  let id_unit = TermInf::Ann(Lam(Inf(Bound(0))), Inf(Pi(Inf(UnitType), Inf(UnitType))))
  // λy. (λx. x) y  and  λy. y  have the same normal form
  let t1 = TermChk::Lam(Inf(App(id_unit, Inf(Bound(0)))))
  let t2 = TermChk::Lam(Inf(Bound(0)))
  assert_true(normal_form(t1) == normal_form(t2))
}
```

The comparison uses the derived `Eq` of `TermChk`, which is $\alpha$-equivalence because names are indices.

### Check under binders yourself

`type_inf_0` covers closed terms. To check a term with free `Bound` variables, call `type_inf` or `type_chk` with the state the checker would have under those binders: the level, a context entry `(Local(k), type)` and an environment entry `val_var(Local(k))` per binder, innermost first.

```moonbit
test "under a binder" {
  // under x : 1, the term x has type 1
  let ctx : @elab.Context = @list.List([(Local(0), VUnitType)])
  let env : @elab.Env = @list.List([@elab.val_var(Local(0))])
  debug_inspect(@elab.type_inf(1, ctx, env, Bound(0)), content="VUnitType")
}
```

## Common pitfalls

- **Type positions must be inferable.** A type is a `TermChk`, but the formation rules infer the universe of a type, so write `Inf(UnitType)`, not a bare `Lam` or `Pair`, wherever a type goes.
- **Functions need annotations to be inferred.** `Lam(...)` can only be checked. Wrap it in `Ann(lam, Inf(Pi(...)))` to use it in an application or as a motive.
- **`W` and `WRec` write the family differently.** In `W(A, B)`, `B` is a body under a binder; in `WRec(A, B, ...)`, `B` is an inferable function term of type $A \to \mathcal U_k$.
- **`def_eq` is directed and context-free.** It tests subtyping, and because it does not know the type of `f` it compares neutral applications such as `f x` by their read-backs, without $\eta$ on the arguments.
- **Evaluation trusts its input.** `eval_inf` and the `val_` functions panic on ill-typed terms; type-check first.
- **Pass closed terms at the top level.** `type_inf_0(ctx, Bound(0))` panics instead of raising `TypeError`, because the index has no binder. Free variables are `Free(Global(...))` entries of the context.
- **Print with `Debug`.** The kernel types derive `Debug`, not `Show`: use `debug_inspect`, `Repr(x)` or `@debug.to_string(x)`. Closures print as `<function: ...>`, so quote a value before printing it.

## Next steps

- The [API reference](../api/elab.md) lists every constructor and function.
- The [design notes](../design/elab.md) give the typing rules in inference-rule notation and explain normalisation by evaluation.
- The treatise linked from the [overview](../index.md) develops the type theory from the untyped lambda calculus.
