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
