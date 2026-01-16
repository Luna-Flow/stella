///|
test "Universe Hierarchy: Inference levels" {
  let ctx = @list.empty()
  inspect(type_inf_0(ctx, Universe(0)), content="VUniverse(1)")
  inspect(type_inf_0(ctx, Universe(1)), content="VUniverse(2)")
}

///|
test "Universe Hierarchy: Max Rule (Pi Types)" {
  let ctx = @list.empty()
  let t_base = TermInf::Pi(Inf(UnitType), Inf(UnitType))
  inspect(type_inf_0(ctx, t_base), content="VUniverse(0)")
  let t_poly = TermInf::Pi(Inf(Universe(0)), Inf(Universe(0)))
  inspect(type_inf_0(ctx, t_poly), content="VUniverse(1)")
  let t_mixed = TermInf::Pi(Inf(UnitType), Inf(Universe(0)))
  inspect(type_inf_0(ctx, t_mixed), content="VUniverse(1)")
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
  let res : Result[Unit, Error] = try? type_chk(
    0,
    @list.empty(),
    @list.empty(),
    term,
    expected,
  )
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
  let res : Result[Unit, Error] = try? type_chk(
    0,
    @list.empty(),
    @list.empty(),
    term,
    expected,
  )
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
  inspect(type_inf_0(ctx, w_term), content="VUniverse(0)")
  let w_lifted = TermInf::W(Inf(Universe(0)), Inf(UnitType))
  inspect(type_inf_0(ctx, w_lifted), content="VUniverse(1)")
}

///|
test "Edge Case: Annotation with higher universe" {
  type_chk(0, @list.empty(), @list.empty(), Inf(UnitType), VUniverse(1)) catch {
    TypeError(msg) =>
      fail("Expected Unit to check against U1, but got error: \{msg}")
  }
}
