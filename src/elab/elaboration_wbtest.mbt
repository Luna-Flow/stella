///|
test "Universe Hierarchy: Inference levels" {
  let ctx = @list.empty()
  debug_inspect(type_inf_0(ctx, Universe(0)), content="VUniverse(1)")
  debug_inspect(type_inf_0(ctx, Universe(1)), content="VUniverse(2)")
}

///|
test "Universe Hierarchy: Max Rule (Pi Types)" {
  let ctx = @list.empty()
  let t_base = TermInf::Pi(Inf(UnitType), Inf(UnitType))
  debug_inspect(type_inf_0(ctx, t_base), content="VUniverse(0)")
  let t_poly = TermInf::Pi(Inf(Universe(0)), Inf(Universe(0)))
  debug_inspect(type_inf_0(ctx, t_poly), content="VUniverse(1)")
  let t_mixed = TermInf::Pi(Inf(UnitType), Inf(Universe(0)))
  debug_inspect(type_inf_0(ctx, t_mixed), content="VUniverse(1)")
}

///|
test "Universe Hierarchy: def_eq logic" {
  assert_eq(def_eq(0, VUniverse(0), VUniverse(1)), true)
  assert_eq(def_eq(0, VUniverse(1), VUniverse(1)), true)
  assert_eq(def_eq(0, VUniverse(1), VUniverse(0)), false)
  assert_eq(def_eq(0, VUnitType, VUniverse(0)), false)
}

///|
test "Subtyping: Pi domain contravariance" {
  let codomain = fn(_ : Value) { VUniverse(0) }
  let wide = VPi(VUniverse(1), codomain)
  let narrow = VPi(VUniverse(0), codomain)
  assert_eq(subtype(0, @list.empty(), wide, narrow), true)
  assert_eq(subtype(0, @list.empty(), narrow, wide), false)
}

///|
test "Subtyping: Pi codomain covariance" {
  let low = VPi(VUniverse(0), fn(_ : Value) { VUniverse(0) })
  let high = VPi(VUniverse(0), fn(_ : Value) { VUniverse(1) })
  assert_eq(subtype(0, @list.empty(), low, high), true)
  assert_eq(subtype(0, @list.empty(), high, low), false)
}

///|
test "Subtyping: Sigma domain invariant" {
  let codomain = fn(_ : Value) { VUniverse(0) }
  let wide = VSigma(VUniverse(1), codomain)
  let narrow = VSigma(VUniverse(0), codomain)
  assert_eq(subtype(0, @list.empty(), wide, narrow), false)
  assert_eq(subtype(0, @list.empty(), narrow, wide), false)
}

///|
test "Subtyping: Sigma codomain covariance" {
  let low = VSigma(VUniverse(0), fn(_ : Value) { VUniverse(0) })
  let high = VSigma(VUniverse(0), fn(_ : Value) { VUniverse(1) })
  assert_eq(subtype(0, @list.empty(), low, high), true)
  assert_eq(subtype(0, @list.empty(), high, low), false)
}

///|
test "Type checking: Pi subtyping via annotation" {
  let term = Inf(
    Ann(Lam(Inf(UnitType)), Inf(Pi(Inf(Universe(1)), Inf(Universe(0))))),
  )
  let expected = VPi(VUniverse(0), fn(_ : Value) { VUniverse(0) })
  type_chk(0, @list.empty(), @list.empty(), term, expected) catch {
    TypeError(msg) =>
      fail("Expected Pi subtyping to hold, but got error: \{msg}")
  }
}

///|
test "Type checking: Pi subtyping rejection" {
  let term = Inf(
    Ann(Lam(Inf(UnitType)), Inf(Pi(Inf(Universe(0)), Inf(Universe(0))))),
  )
  let expected = VPi(VUniverse(1), fn(_ : Value) { VUniverse(0) })
  let res : Result[Unit, Error] = try
    type_chk(0, @list.empty(), @list.empty(), term, expected)
  catch {
    e => Err(e)
  } noraise {
    v => Ok(v)
  }
  guard res is Err(TypeError(_)) else {
    fail("Expected Pi subtyping to be rejected")
  }
}

///|
test "Type checking: Sigma domain mismatch rejection" {
  let term = Inf(
    Ann(
      Pair(Inf(Universe(0)), Inf(UnitType)),
      Inf(Sigma(Inf(Universe(1)), Inf(Universe(0)))),
    ),
  )
  let expected = VSigma(VUniverse(0), fn(_ : Value) { VUniverse(0) })
  let res : Result[Unit, Error] = try
    type_chk(0, @list.empty(), @list.empty(), term, expected)
  catch {
    e => Err(e)
  } noraise {
    v => Ok(v)
  }
  guard res is Err(TypeError(_)) else {
    fail("Expected Sigma domain invariance to be enforced")
  }
}

///|
test "Type checking: Sigma codomain covariance" {
  let term = Inf(
    Ann(
      Pair(Inf(UnitType), Inf(UnitType)),
      Inf(Sigma(Inf(Universe(0)), Inf(Universe(0)))),
    ),
  )
  let expected = VSigma(VUniverse(0), fn(_ : Value) { VUniverse(1) })
  type_chk(0, @list.empty(), @list.empty(), term, expected) catch {
    TypeError(msg) =>
      fail("Expected Sigma codomain subtyping, but got error: \{msg}")
  }
}

///|
test "Universe Hierarchy: W-Types" {
  let ctx = @list.empty()
  let w_term = TermInf::W(Inf(UnitType), Inf(UnitType))
  debug_inspect(type_inf_0(ctx, w_term), content="VUniverse(0)")
  let w_lifted = TermInf::W(Inf(Universe(0)), Inf(UnitType))
  debug_inspect(type_inf_0(ctx, w_lifted), content="VUniverse(1)")
}

///|
test "Edge Case: Annotation with higher universe" {
  type_chk(0, @list.empty(), @list.empty(), Inf(UnitType), VUniverse(1)) catch {
    TypeError(msg) =>
      fail("Expected Unit to check against U1, but got error: \{msg}")
  }
}

///|
fn j_fixture_refl_tt() -> TermInf {
  let unit_ty : TermChk = Inf(UnitType)
  Ann(Rfl(UnitElement), Inf(Id(unit_ty, UnitElement, UnitElement)))
}

///|
fn j_rejects(motive : TermChk) -> Bool {
  let unit_ty : TermChk = Inf(UnitType)
  let term = JElim(
    unit_ty,
    UnitElement,
    motive,
    UnitElement,
    UnitElement,
    j_fixture_refl_tt(),
  )
  let res : Result[Value, Error] = try type_inf_0(@list.empty(), term) catch {
    e => Err(e)
  } noraise {
    v => Ok(v)
  }
  res is Err(TypeError(_))
}

///|
test "J: well-typed motive is accepted" {
  let unit_ty : TermChk = Inf(UnitType)
  // motive : Π(y : Unit). Id(Unit, tt, y) → U0 := λy. λq. Unit
  let motive_ty : TermChk = Inf(
    Pi(
      unit_ty,
      Inf(Pi(Inf(Id(unit_ty, UnitElement, Inf(Bound(0)))), Inf(Universe(0)))),
    ),
  )
  let motive : TermChk = Inf(Ann(Lam(Lam(unit_ty)), motive_ty))
  let term = JElim(
    unit_ty,
    UnitElement,
    motive,
    UnitElement,
    UnitElement,
    j_fixture_refl_tt(),
  )
  assert_true(type_inf_0(@list.empty(), term) is VUnitType)
}

///|
test "J: motive whose first domain does not accept A is rejected" {
  // motive : U0 → U0 → U0, used with A = Unit (issue #19)
  let u0 : TermChk = Inf(Universe(0))
  let motive_ty : TermChk = Inf(Pi(u0, Inf(Pi(u0, u0))))
  let motive : TermChk = Inf(Ann(Lam(Lam(Inf(UnitType))), motive_ty))
  assert_true(j_rejects(motive))
}

///|
test "J: motive that would eliminate its argument is rejected, not crashed" {
  // motive : (Unit → Unit) → Unit → U0 := λf. λq. Id(Unit, f tt, tt) (issue #19)
  let unit_ty : TermChk = Inf(UnitType)
  let motive_ty : TermChk = Inf(
    Pi(Inf(Pi(unit_ty, unit_ty)), Inf(Pi(unit_ty, Inf(Universe(0))))),
  )
  let body : TermChk = Inf(
    Id(unit_ty, Inf(App(Bound(1), UnitElement)), UnitElement),
  )
  let motive : TermChk = Inf(Ann(Lam(Lam(body)), motive_ty))
  assert_true(j_rejects(motive))
}

///|
test "J: motive whose second domain is not Id(A, x, y) is rejected" {
  // motive : Π(y : Unit). Unit → U0 — second domain ignores the path type
  let unit_ty : TermChk = Inf(UnitType)
  let motive_ty : TermChk = Inf(Pi(unit_ty, Inf(Pi(unit_ty, Inf(Universe(0))))))
  let motive : TermChk = Inf(Ann(Lam(Lam(unit_ty)), motive_ty))
  assert_true(j_rejects(motive))
}

///|
test "def_eq: reflexive on neutral applications (#18)" {
  let f_tt = eval_inf(App(Free(Global("f")), UnitElement), @list.empty())
  assert_true(def_eq(0, f_tt, f_tt))
  let f_u = eval_inf(
    App(Free(Global("f")), Inf(Free(Global("u")))),
    @list.empty(),
  )
  assert_true(def_eq(0, f_u, f_u))
  assert_false(def_eq(0, f_tt, f_u))
}

///|
fn rfl_ctx() -> Context {
  @list.List([
    (Global("f"), VPi(VUnitType, fn(_ : Value) { VUnitType })),
    (Global("u"), VUnitType),
  ])
}

///|
fn accepts(ctx : Context, term : TermInf) -> Bool {
  let res : Result[Value, Error] = try type_inf_0(ctx, term) catch {
    e => Err(e)
  } noraise {
    v => Ok(v)
  }
  res is Ok(_)
}

///|
test "Rfl: endpoints compared by conversion with eta (#20)" {
  let unit_ty : TermChk = Inf(UnitType)
  let fn_ty : TermChk = Inf(Pi(unit_ty, unit_ty))
  let f : TermInf = Free(Global("f"))
  let eta_f : TermChk = Lam(Inf(App(f, Inf(Bound(0)))))
  // refl f : Id(1 → 1, f, λx. f x)  — η for functions
  assert_true(
    accepts(rfl_ctx(), Ann(Rfl(Inf(f)), Inf(Id(fn_ty, Inf(f), eta_f)))),
  )
  // refl tt : Id(1, tt, u)  — η for Unit
  assert_true(
    accepts(
      rfl_ctx(),
      Ann(
        Rfl(UnitElement),
        Inf(Id(unit_ty, UnitElement, Inf(Free(Global("u"))))),
      ),
    ),
  )
  // endpoints that are not convertible are still rejected:
  // refl Unit : Id(U0, Unit, Unit → Unit)
  assert_false(
    accepts(
      rfl_ctx(),
      Ann(
        Rfl(unit_ty),
        Inf(Id(Inf(Universe(0)), unit_ty, Inf(Pi(unit_ty, unit_ty)))),
      ),
    ),
  )
}

///|
test "quote: stuck WRec reads back to a term that evaluates to itself (#21)" {
  let unit_ty : TermChk = Inf(UnitType)
  let arr = fn(a : TermChk, b : TermChk) -> TermChk { Inf(Pi(a, b)) }
  let b_fun : TermChk = Inf(Ann(Lam(unit_ty), arr(unit_ty, Inf(Universe(0)))))
  let w_ty : TermChk = Inf(W(unit_ty, unit_ty))
  let motive : TermChk = Inf(Ann(Lam(unit_ty), arr(w_ty, Inf(Universe(0)))))
  let t : TermInf = WRec(
    unit_ty,
    b_fun,
    motive,
    Lam(Lam(Lam(UnitElement))),
    Free(Global("w")),
  )
  let q1 = quote(0, eval_inf(t, @list.empty()))
  guard q1 is Inf(WRec(_, Lam(_), _, _, _) as t1) else {
    fail("expected B to be read back as a function")
  }
  let q2 = quote(0, eval_inf(t1, @list.empty()))
  assert_eq(q1, q2)
}
