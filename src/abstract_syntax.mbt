///|
pub(all) enum Name {
  Global(String)
  Local(Int)
  Quote(Int)
} derive(Show, Eq)

///|
pub(all) enum TermChk {
  Inf(TermInf)
  Lam(TermChk)
  Pair(TermChk, TermChk)
  UnitElement
  Rfl(TermChk)
  /// Sup(shape, children)
  Sup(TermChk, TermChk)
} derive(Show, Eq)

///|
pub(all) enum TermInf {
  Ann(TermChk, TermChk)
  Star
  Pi(TermChk, TermChk)
  Sigma(TermChk, TermChk)
  Bound(Int)
  Free(Name)
  App(TermInf, TermChk)
  Fst(TermInf)
  Snd(TermInf)
  UnitType
  /// Id(A, x, y)
  Id(TermChk, TermChk, TermChk)
  /// JElim(A, x, motive, base_case, y, p)
  JElim(TermChk, TermChk, TermChk, TermChk, TermChk, TermInf)
  /// W(A, B)
  W(TermChk, TermChk)
  /// WRec(A, B, motive, step_case, target)
  WRec(TermChk, TermChk, TermChk, TermChk, TermInf)
} derive(Show, Eq)

///|
pub(all) enum Neutral {
  NFree(Name)
  NApp(Neutral, Value)
  NFst(Neutral)
  NSnd(Neutral)
  NJElim(Value, Value, Value, Value, Value, Neutral)
  NWRec(Value, (Value) -> Value, Value, Value, Neutral)
}

///|
pub(all) enum Value {
  VLam((Value) -> Value)
  VStar
  VPi(Value, (Value) -> Value)
  VSigma(Value, (Value) -> Value)
  VPair(Value, Value)
  VNeutral(Neutral)
  VUnitType
  VUnitElement
  VId(Value, Value, Value)
  VRfl(Value)
  VW(Value, (Value) -> Value)
  VSup(Value, (Value) -> Value)
}

///|
pub type Type = Value

///|
pub type Context = @list.List[(Name, Type)]
