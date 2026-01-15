///|
pub(all) enum Name {
  Global(String)
  Local(Int)
  Quote(Int)
} derive(Show, Eq)

///|
pub(all) enum TermChk {
  Inf(TermInf)
  UnitElement
  Lam(TermChk)
  Pair(TermChk, TermChk)
  Rfl(TermChk)
  /// Sup(shape, children)
  Sup(TermChk, TermChk)
} derive(Show, Eq)

///|
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
} derive(Show)

///|
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
} derive(Show)

///|
pub type Type = Value

///|
pub type Context = @list.List[(Name, Type)]
