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
} derive(Show, Eq)

///|
pub(all) enum TermInf {
  Ann(TermChk, TermChk)
  Star
  Pi(TermChk, TermChk)
  Bound(Int)
  Free(Name)
  App(TermInf, TermChk)
} derive(Show, Eq)

///|
pub(all) enum Neutral {
  NFree(Name)
  NApp(Neutral, Value)
}

///|
pub(all) enum Value {
  VLam((Value) -> Value)
  VStar
  VPi(Value, (Value) -> Value)
  VNeutral(Neutral)
}

///|
pub typealias Value as Type

///|
pub type Context = @list.List[(Name, Type)]
