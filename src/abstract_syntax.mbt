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
} derive(Show, Eq)

///|
pub(all) enum Neutral {
  NFree(Name)
  NApp(Neutral, Value)
  NFst(Neutral)
  NSnd(Neutral)
}

///|
pub(all) enum Value {
  VLam((Value) -> Value)
  VStar
  VPi(Value, (Value) -> Value)
  VSigma(Value, (Value) -> Value)
  VPair(Value, Value)
  VNeutral(Neutral)
}

///|
pub typealias Value as Type

///|
pub type Context = @list.List[(Name, Type)]
