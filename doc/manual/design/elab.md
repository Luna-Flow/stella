# elab design

The `elab` package is the kernel of stella. It implements a dependent type theory in the style of Martin-Löf with a unit type, $\Pi$, $\Sigma$, identity and W types and a cumulative hierarchy of universes, and it decides typing with a bidirectional checker whose definitional equality is computed by normalisation by evaluation (NbE). This page states the rules the code implements, derives the properties that make them work, and records where the implementation is incomplete.

## Design goal

- A small, readable kernel whose structure mirrors the theory: one function per judgement, one match arm per rule.
- Decidable checking with few annotations: the user annotates only where the checker cannot infer.
- Equality of types by computation: two types are compared by evaluating them and comparing normal forms, not by rewriting syntax.
- An implementation close to the references the project follows: Löh, McBride and Swierstra's tutorial implementation $\lambda\Pi$ and Norell's thesis on Agda.[^refs]

[^refs]: A. Löh, C. McBride, W. Swierstra, "A tutorial implementation of a dependently typed lambda calculus", *Fundamenta Informaticae* 102 (2010). U. Norell, *Towards a practical programming language based on dependent type theory*, PhD thesis, Chalmers (2007).

## Mathematical background

### Syntax

Terms are split by the judgement that handles them. Writing $e$ for inferable terms (`TermInf`) and $t$ for checkable terms (`TermChk`):

$$
\begin{aligned}
e \;::=\;& \#i \mid x \mid \mathbf 1 \mid \mathcal U_i \mid (t : t) \mid \Pi(t, t) \mid e\;t \mid \Sigma(t, t) \mid \pi_1 e \mid \pi_2 e \\
 \mid\;& \mathrm{Id}(t, t, t) \mid J(t, t, t, t, t, e) \mid W(t, t) \mid \mathrm{wrec}(t, t, t, t, e) \\
t \;::=\;& e \mid \star \mid \lambda.\,t \mid (t, t) \mid \mathrm{refl}\;t \mid \sup(t, t)
\end{aligned}
$$

Bound variables are de Bruijn indices $\#i$ (`Bound(i)`): $\#0$ refers to the nearest enclosing binder. The binders are $\lambda$ and the second argument of $\Pi$, $\Sigma$ and $W$. Because a bound variable has no name, two terms are $\alpha$-equivalent exactly when they are equal as trees, so the derived `Eq` of `TermInf` and `TermChk` *is* $\alpha$-equivalence.

### Values and neutral terms

Evaluation maps terms into a semantic domain $D$ (`Value`):

$$
\begin{aligned}
v, A \;::=\;& \underline{n} \mid \mathbf 1 \mid \star \mid \mathcal U_i \mid \lambda f \mid \Pi(A, F) \mid \Sigma(A, F) \mid (v, v) \mid \mathrm{Id}(A, v, v) \mid \mathrm{refl}\;v \mid W(A, F) \mid \sup(v, F) \\
n \;::=\;& x \mid n\;v \mid \pi_1 n \mid \pi_2 n \mid J(A, v, v, v, v, n) \mid \mathrm{wrec}(A, F, v, v, n)
\end{aligned}
$$

where $f, F : D \to D$ are MoonBit functions. A binder body becomes a function on values: $\Pi(A, F)$ is the type $\Pi_{x : A} F(x)$. The neutral terms $n$ (`Neutral`) are eliminations stuck on a free variable $x$.

Every value is in weak head normal form: no elimination is applied to an introduction form, because the evaluator reduces such redexes as soon as it builds them.

### Evaluation

Evaluation $\llbracket t \rrbracket_\rho$ (`eval_inf`, `eval_chk`) takes an environment $\rho$ whose $i$-th entry is the value of $\#i$:

$$
\begin{aligned}
\llbracket \#i \rrbracket_\rho &= \rho(i) &
\llbracket (t : T) \rrbracket_\rho &= \llbracket t \rrbracket_\rho \\
\llbracket \lambda.\,t \rrbracket_\rho &= \lambda\bigl(v \mapsto \llbracket t \rrbracket_{v :: \rho}\bigr) &
\llbracket \Pi(A, B) \rrbracket_\rho &= \Pi\bigl(\llbracket A \rrbracket_\rho,\; v \mapsto \llbracket B \rrbracket_{v :: \rho}\bigr) \\
\llbracket e\;t \rrbracket_\rho &= \llbracket e \rrbracket_\rho \cdot \llbracket t \rrbracket_\rho &
\llbracket \pi_k e \rrbracket_\rho &= \pi_k \cdot \llbracket e \rrbracket_\rho
\end{aligned}
$$

and similarly for the other constructors. The semantic eliminations (`val_app`, `val_fst`, `val_snd`, `val_j_elim`, `val_w_rec`) carry the computation rules:

$$
\begin{aligned}
(\lambda f) \cdot v &= f(v) && (\beta) \\
\pi_1 \cdot (v, w) = v, \qquad \pi_2 \cdot (v, w) &= w && (\Sigma\beta) \\
J(A, x, P, d, y, \mathrm{refl}\;z) &= d && (J\beta) \\
\mathrm{wrec}(A, B, P, s, \sup(a, f)) &= s \cdot a \cdot \lambda f \cdot \lambda\bigl(z \mapsto \mathrm{wrec}(A, B, P, s, f(z))\bigr) && (W\beta)
\end{aligned}
$$

and on a neutral argument they extend the spine, for example $\underline{n} \cdot v = \underline{n\;v}$. Annotations are erased.

### Read-back and normal forms

Read-back $q_l$ (`quote`, `neutral_quote`) turns a value under $l$ binders into a term. A function is read back by applying it to a fresh variable:

$$
q_l(\lambda f) = \lambda.\; q_{l+1}\bigl(f(\underline{\mathsf{Quote}(l)})\bigr), \qquad
q_l\bigl(\Pi(A, F)\bigr) = \Pi\bigl(q_l(A),\; q_{l+1}(F(\underline{\mathsf{Quote}(l)}))\bigr),
$$

and a fresh variable is turned back into an index:

$$
q_l\bigl(\underline{\mathsf{Quote}(k)}\bigr) = \#(l - k - 1).
$$

*Why $l - k - 1$.* Read-back numbers binders by *level*, from the outside: the binder opened at depth $k$ introduces $\mathsf{Quote}(k)$. At depth $l$, the binders opened after it have levels $k + 1, \dots, l - 1$, so $l - 1 - k$ binders lie between the occurrence and its binder, which is its de Bruijn *index*. The variable is fresh because at depth $l$ only $\mathsf{Quote}(0), \dots, \mathsf{Quote}(l-1)$ are in scope. Levels make freshness trivial (no renaming, no shifting), and indices make the output canonical.

The *normal form* of a closed term is $\mathrm{nf}(t) = q_0(\llbracket t \rrbracket_\varepsilon)$.

### Why evaluation respects $\beta$

The central lemma of NbE is that $\beta$-equal terms have the same value. For a redex,

$$
\begin{aligned}
\llbracket (\lambda.\,t : T)\;u \rrbracket_\rho
&= \llbracket \lambda.\,t \rrbracket_\rho \cdot \llbracket u \rrbracket_\rho \\
&= \bigl(v \mapsto \llbracket t \rrbracket_{v :: \rho}\bigr)\bigl(\llbracket u \rrbracket_\rho\bigr) \\
&= \llbracket t \rrbracket_{\llbracket u \rrbracket_\rho :: \rho} \\
&= \llbracket t[u / \#0] \rrbracket_\rho ,
\end{aligned}
$$

where the last step is the substitution lemma, proved by induction on $t$: substituting $u$ for $\#0$ and evaluating in $\rho$ gives the same value as evaluating in $\rho$ extended with the value of $u$. The same computation for the other redexes uses $\Sigma\beta$, $J\beta$ and $W\beta$ above. Since the value of a term depends only on its $\beta$-class, so does its normal form: $t =_\beta u \Rightarrow \mathrm{nf}(t) = \mathrm{nf}(u)$. Conversely, $\mathrm{nf}(t)$ is reached from $t$ by $\beta$-steps, so equal normal forms imply $\beta$-equality. Together these make "compare normal forms" a decision procedure for $\beta$-equality on terms whose evaluation terminates.[^nbe]

[^nbe]: U. Berger and H. Schwichtenberg, "An inverse of the evaluation functional for typed λ-calculus", LICS 1991, introduced NbE. A. Abel, *Normalization by Evaluation: Dependent Types and Impredicativity*, habilitation, LMU Munich (2013), proves soundness and completeness of NbE for Martin-Löf type theory with $\eta$. These are results about the theory; for this implementation they are tested, not proved.

### The bidirectional judgements

The checker has two judgements, each a function:

- $\Gamma; \rho \vdash_l e \Rightarrow A$ (*inference*, `type_inf`): $e$ has type $A$, which the checker computes;
- $\Gamma; \rho \vdash_l t \Leftarrow A$ (*checking*, `type_chk`): $t$ has the given type $A$.

The context $\Gamma$ maps names to types (values), $\rho$ is the environment of the current position, and $l$ counts the binders entered. Under a binder the checker extends all three with a fresh variable $x_l = \underline{\mathsf{Local}(l)}$: it writes $\Gamma, x_l : A;\ \rho, x_l \vdash_{l+1}$. Thus $\rho$ always maps $\#i$ to the variable $x_{l-1-i}$, and $\Gamma$ gives its type. Below, $\llbracket t \rrbracket$ abbreviates $\llbracket t \rrbracket_\rho$.

**Variables, constants and annotations.**

$$
\dfrac{\rho(i) = \underline{x} \qquad (x : A) \in \Gamma}{\Gamma; \rho \vdash \#i \Rightarrow A}\;(\textsf{Var})
\qquad
\dfrac{(x : A) \in \Gamma}{\Gamma; \rho \vdash x \Rightarrow A}\;(\textsf{Free})
\qquad
\dfrac{\Gamma; \rho \vdash T \Rightarrow \mathcal U_j \qquad \Gamma; \rho \vdash t \Leftarrow \llbracket T \rrbracket}{\Gamma; \rho \vdash (t : T) \Rightarrow \llbracket T \rrbracket}\;(\textsf{Ann})
$$

**Universes and type formers.** Here and below, a premise $T \Rightarrow \mathcal U_i$ requires $T$ to be an inferable term whose inferred type *is* a universe; there is no subsumption in these premises.

$$
\dfrac{}{\Gamma; \rho \vdash \mathbf 1 \Rightarrow \mathcal U_0}\;(\mathbf 1\textsf{-F})
\qquad
\dfrac{}{\Gamma; \rho \vdash \mathcal U_i \Rightarrow \mathcal U_{i+1}}\;(\mathcal U\textsf{-F})
\qquad
\dfrac{\Gamma; \rho \vdash_l A \Rightarrow \mathcal U_i \qquad \Gamma, x_l : \llbracket A \rrbracket;\ \rho, x_l \vdash_{l+1} B \Rightarrow \mathcal U_j}{\Gamma; \rho \vdash_l \Pi(A, B) \Rightarrow \mathcal U_{\max(i, j)}}\;(\Pi\textsf{-F})
$$

The rules $(\Sigma\textsf{-F})$ and $(W\textsf{-F})$ are the same with $\Sigma$ and $W$ in place of $\Pi$. The identity type lives in the universe of its carrier:

$$
\dfrac{\Gamma; \rho \vdash A \Rightarrow \mathcal U_i \qquad \Gamma; \rho \vdash x \Leftarrow \llbracket A \rrbracket \qquad \Gamma; \rho \vdash y \Leftarrow \llbracket A \rrbracket}{\Gamma; \rho \vdash \mathrm{Id}(A, x, y) \Rightarrow \mathcal U_i}\;(\mathrm{Id}\textsf{-F})
$$

**Introductions are checked.** The expected type supplies what the term omits, such as the domain of a $\lambda$:

$$
\dfrac{\Gamma, x_l : A;\ \rho, x_l \vdash_{l+1} t \Leftarrow F(x_l)}{\Gamma; \rho \vdash_l \lambda.\,t \Leftarrow \Pi(A, F)}\;(\Pi\textsf{-I})
\qquad
\dfrac{\Gamma; \rho \vdash t \Leftarrow A \qquad \Gamma; \rho \vdash u \Leftarrow F(\llbracket t \rrbracket)}{\Gamma; \rho \vdash (t, u) \Leftarrow \Sigma(A, F)}\;(\Sigma\textsf{-I})
\qquad
\dfrac{}{\Gamma; \rho \vdash \star \Leftarrow \mathbf 1}\;(\mathbf 1\textsf{-I})
$$

$$
\dfrac{\Gamma; \rho \vdash_l t \Leftarrow A \qquad q_l(\llbracket t \rrbracket) = q_l(v) = q_l(w)}{\Gamma; \rho \vdash_l \mathrm{refl}\;t \Leftarrow \mathrm{Id}(A, v, w)}\;(\mathrm{Id}\textsf{-I})
\qquad
\dfrac{\Gamma; \rho \vdash a \Leftarrow A \qquad \Gamma; \rho \vdash f \Leftarrow \Pi\bigl(F(\llbracket a \rrbracket),\ \_ \mapsto W(A, F)\bigr)}{\Gamma; \rho \vdash \sup(a, f) \Leftarrow W(A, F)}\;(W\textsf{-I})
$$

**Eliminations are inferred.** The type of the eliminated term is inferred and then taken apart:

$$
\dfrac{\Gamma; \rho \vdash f \Rightarrow \Pi(A, F) \qquad \Gamma; \rho \vdash t \Leftarrow A}{\Gamma; \rho \vdash f\;t \Rightarrow F(\llbracket t \rrbracket)}\;(\Pi\textsf{-E})
\qquad
\dfrac{\Gamma; \rho \vdash e \Rightarrow \Sigma(A, F)}{\Gamma; \rho \vdash \pi_1 e \Rightarrow A}\;(\Sigma\textsf{-E}_1)
\qquad
\dfrac{\Gamma; \rho \vdash e \Rightarrow \Sigma(A, F)}{\Gamma; \rho \vdash \pi_2 e \Rightarrow F(\pi_1 \cdot \llbracket e \rrbracket)}\;(\Sigma\textsf{-E}_2)
$$

Path induction, with the motive $P$ inferred and $\bar A = \llbracket A \rrbracket$, $\bar x = \llbracket x \rrbracket$, $\bar y = \llbracket y \rrbracket$, $\bar P = \llbracket P \rrbracket$:

$$
\dfrac{
\begin{gathered}
\Gamma; \rho \vdash A \Rightarrow \mathcal U_i \qquad
\Gamma; \rho \vdash x \Leftarrow \bar A \qquad
\Gamma; \rho \vdash y \Leftarrow \bar A \qquad
\Gamma; \rho \vdash p \Leftarrow \mathrm{Id}(\bar A, \bar x, \bar y) \\
\Gamma; \rho \vdash P \Rightarrow \Pi(D_1, F_1) \qquad
\Gamma \vdash_l \bar A \le D_1 \\
F_1(z) = \Pi(D_2, F_2) \qquad
\Gamma, z : \bar A \vdash_{l+1} \mathrm{Id}(\bar A, \bar x, z) \le D_2 \qquad
F_2(w) = \mathcal U_k \qquad
\Gamma; \rho \vdash d \Leftarrow \bar P \cdot \bar x \cdot \mathrm{refl}\;\bar x
\end{gathered}
}{\Gamma; \rho \vdash J(A, x, P, d, y, p) \Rightarrow \bar P \cdot \bar y \cdot \llbracket p \rrbracket}\;(J)
$$

The universe level $k$ of the motive is inferred rather than fixed, which is what cumulative universes need. The two domains are still checked: $P$ is only ever applied to a point of $\bar A$ and to a path out of $\bar x$, so its domains must accept those arguments, and $\Pi$ is contravariant in its domain. Checking only the shape $\Pi(D_1, \Pi(D_2, \mathcal U_k))$ would let $P$ be applied to arguments of the wrong type during checking.

W recursion, where $B$ is an inferable *function* $A \to \mathcal U_k$, $\bar B(v) = \llbracket B \rrbracket \cdot v$ and $\bar W = W(\bar A, \bar B)$:

$$
\dfrac{
\begin{gathered}
\Gamma; \rho \vdash A \Rightarrow \mathcal U_i \qquad
\Gamma; \rho \vdash B \Rightarrow \Pi(D, G),\ q_l(D) = q_l(\bar A),\ G(z) = \mathcal U_k \qquad
\Gamma; \rho \vdash w \Leftarrow \bar W \\
\Gamma; \rho \vdash P \Rightarrow \Pi(D', G'),\ q_l(D') = q_l(\bar W),\ G'(z) = \mathcal U_m \qquad
\Gamma; \rho \vdash s \Leftarrow \Pi_{a : \bar A}\, \Pi_{f : \bar B(a) \to \bar W}\, \Pi_{h : \Pi_{b : \bar B(a)} \bar P \cdot f(b)}\; \bar P \cdot \sup(a, f)
\end{gathered}
}{\Gamma; \rho \vdash \mathrm{wrec}(A, B, P, s, w) \Rightarrow \bar P \cdot \llbracket w \rrbracket}\;(W\textsf{-E})
$$

**Changing direction.** An inferable term is accepted in checking mode when its type is a subtype of the expected one:

$$
\dfrac{\Gamma; \rho \vdash_l e \Rightarrow A' \qquad \Gamma \vdash_l A' \le A}{\Gamma; \rho \vdash_l e \Leftarrow A}\;(\textsf{Sub})
$$

The opposite direction is $(\textsf{Ann})$: a checkable term becomes inferable once its type is written down.

### Subtyping and conversion

The relation $A \le A'$ (`subtype_nf`, exposed for the empty context as `def_eq`) is cumulativity:

$$
\dfrac{i \le j}{\mathcal U_i \le \mathcal U_j}
\qquad
\dfrac{A' \le A \qquad \Gamma, x_l : A' \vdash_{l+1} F(x_l) \le F'(x_l)}{\Gamma \vdash_l \Pi(A, F) \le \Pi(A', F')}
\qquad
\dfrac{A \equiv A' \qquad \Gamma, x_l : A \vdash_{l+1} F(x_l) \le F'(x_l)}{\Gamma \vdash_l \Sigma(A, F) \le \Sigma(A', F')}
\qquad
\dfrac{A \equiv A'}{A \le A'}
$$

The $\Pi$ rule is contravariant in the domain: a function that accepts every element of $A$ accepts every element of a subtype $A' \le A$, and its results in $F(x)$ are also results in the supertype $F'(x)$. The $\Sigma$ rule keeps the first component *invariant*; covariance would also be sound, but the implementation, and its tests, require conversion there.

Conversion $A \equiv A'$ (`conv_type`) compares types structurally, entering binders with a fresh variable, and compares the endpoints of identity types with the type-directed $\equiv_A$ (`conv_nf`), which adds $\eta$:

$$
f \equiv_{\Pi(A, F)} g \iff f \cdot x_l \equiv_{F(x_l)} g \cdot x_l, \qquad
p \equiv_{\Sigma(A, F)} r \iff \pi_1 p \equiv_A \pi_1 r \;\wedge\; \pi_2 p \equiv_{F(\pi_1 p)} \pi_2 r, \qquad
u \equiv_{\mathbf 1} u'.
$$

Neutral terms are compared spine by spine (`conv_neu`), looking up the type of the head variable in $\Gamma$ to compare application arguments at the right type. Everything else falls back to comparing read-backs, $q_l(v) = q_l(v')$.

### Universes

The universes are *predicative* and *Russell style*: a type is itself a term, and $\mathcal U_i : \mathcal U_{i+1}$. There is no rule $\mathcal U_i : \mathcal U_i$, because a universe containing itself makes the theory inconsistent (Girard's paradox).[^girard] A type former lands in the larger universe of its parts, $\max(i, j)$, which is what predicativity requires: $\Pi_{A : \mathcal U_0} A \to A$ quantifies over $\mathcal U_0$ and therefore lives in $\mathcal U_1$. Cumulativity $\mathcal U_i \le \mathcal U_{i+1}$ is not a typing rule but part of subtyping, used by $(\textsf{Sub})$.

[^girard]: J.-Y. Girard, *Interprétation fonctionnelle et élimination des coupures de l'arithmétique d'ordre supérieur*, thèse d'État (1972); a short proof is A. J. C. Hurkens, "A simplification of Girard's paradox", TLCA 1995.

## Design decisions

### Bidirectional checking

**Problem.** Inferring the type of an unannotated $\lambda$ in a dependent type theory requires guessing its domain, which in general means higher-order unification, which is undecidable.

**Options.** (a) Annotate every binder, $\lambda (x : A).\,t$. (b) Infer with unification variables. (c) Split the terms into checked and inferred ones.

**Choice.** (c). Introduction forms ($\lambda$, pairs, $\star$, $\mathrm{refl}$, $\sup$) are checked, because their type determines the missing information; eliminations and type formers are inferred, because the type of the head determines the type of the whole. An annotation is needed only where an introduction meets an elimination, that is, at a $\beta$-redex such as $(\lambda.\,t : T)\;u$, or where a motive must be a function. A term in normal form needs no annotations at all apart from the motives. Encoding the split in the types `TermInf` and `TermChk` makes an unannotated redex unrepresentable rather than a runtime error.

### Values with closures

**Problem.** Comparing types requires evaluating them, including under binders.

**Options.** (a) Rewrite syntax by substitution, which needs capture-avoiding substitution and index shifting at every step. (b) Evaluate into a semantic domain where binders are host functions.

**Choice.** (b). A body is represented by a MoonBit function `(Value) -> Value`, so $\beta$-reduction is a host function call and substitution never happens on syntax. Read-back recovers syntax only when needed: for printing, for comparison by $q_l$, and in the checks that compare normal forms.

### Indices in terms, levels in values

Terms use indices, so that $\alpha$-equivalence is structural equality and closed subterms do not depend on their position. Fresh variables in values use levels, `Local(l)` for the checker and `Quote(l)` for read-back, so that creating a fresh variable is a counter increment and values never need shifting. The two kinds of fresh variable are separate `Name` constructors, so a variable introduced by the checker cannot be mistaken for one introduced while reading back.

### Subtyping instead of explicit lifts

Cumulativity could be expressed with explicit lifting operators $\uparrow : \mathcal U_i \to \mathcal U_{i+1}$. Building it into the change of direction $(\textsf{Sub})$ instead means a type written in $\mathcal U_0$ can be used in $\mathcal U_1$ without any term-level coercion, as in `type_chk(..., Inf(UnitType), VUniverse(1))`.

## Correctness and invariants

1. **Environment invariant.** At level $l$, `env` has exactly $l$ entries, entry $i$ is $x_{l-1-i}$, and `ctx` declares every $x_k$. The rules that go under a binder are the only places that extend the state, and they extend all three together. $(\textsf{Var})$ relies on this invariant; a caller of `type_inf` that breaks it gets `Internal error: Bound variable not in environment`.
2. **Evaluate only what has been checked.** In every rule, a subterm is evaluated after the premise that checks it, for example the argument in $(\Pi\textsf{-E})$ and the type in $(\textsf{Ann})$. Since the evaluator panics on ill-typed redexes, this ordering is what keeps the checker total on ill-typed input: it raises `TypeError` before it evaluates.
3. **Stability of types.** Every type the checker returns is a value, so the caller never has to normalise it again, and every comparison of types happens on values.
4. **Termination.** Evaluation of a well-typed term terminates by the normalisation theorem for Martin-Löf type theory with W types and predicative universes. The checker only evaluates checked terms (invariant 2), so it terminates on every input for which its rules are sound; the gaps listed below are the exceptions.

### Known gaps

The implementation is a work in progress, and some rules are weaker or stronger than the theory above. They are recorded here so that users can avoid them; the code is unchanged.

- **`def_eq` uses an empty context.** It cannot look up the types of free variables, so `conv_neu` cannot compare the arguments of two neutral applications, and `def_eq(0, f x, f x)` returns `false` for a free `f`. Inside the checker, where the context is available, the comparison succeeds.
- **$\mathrm{refl}$ compares read-backs without $\eta$.** $(\mathrm{Id}\textsf{-I})$ compares $q_l$ syntactically, so $\mathrm{refl}\;f : \mathrm{Id}(\mathbf 1 \to \mathbf 1, f, \lambda.\,f\,\#0)$ is rejected even though the two endpoints are $\eta$-equal. The same holds for the domain checks in $(W\textsf{-E})$.
- **Read-back of a stuck `wrec` is not re-evaluable.** `neutral_quote` writes the family $B$ of an `NWRec` as a body under a binder, but `WRec` expects $B$ as a function term, so $\llbracket q_l(v) \rrbracket$ can differ from $v$ for such values.
- **Subtyping only for $\Pi$, $\Sigma$ and universes.** $W$ and identity types are compared by conversion, without cumulativity in their components.

## Alternatives rejected

- **Typed terms with names.** Named variables need capture-avoiding substitution and make $\alpha$-equivalence a separate check; de Bruijn indices avoid both.
- **Substitution-based normalisation.** Repeated syntactic substitution is slower and harder to get right than evaluation into closures, and it still needs a separate conversion check.
- **Impredicative or self-containing universes.** $\mathcal U : \mathcal U$ is inconsistent, and an impredicative $\mathrm{Prop}$ is not part of the theory stella follows.
- **Inductive families.** W types provide well-founded trees with a single eliminator, which keeps the kernel small; general inductive definitions would need a positivity checker.

## Boundaries

The package deliberately does not:

- parse a surface syntax, elaborate implicit arguments or solve unification problems; terms are built as MoonBit values in core syntax;
- support definitions, `let` or global definitions with bodies; the context holds postulates (names with types) only;
- provide universe polymorphism, inductive families, an empty type or sum types;
- implement univalence, higher inductive types or any other feature of homotopy type theory, although the treatise describes them as goals of the project;
- guarantee anything for ill-typed input to the evaluator; `eval_inf`, `eval_chk` and the `val_` functions may panic.
