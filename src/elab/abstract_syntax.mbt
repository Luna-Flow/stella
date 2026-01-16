///|
/// Variable name identifier in the abstract syntax tree.
///
/// Constructors:
///
/// * `Global(String)` : Global variable with a string name identifier.
/// * `Local(Int)` : Local variable with a de Bruijn index.
/// * `Quote(Int)` : Quoted variable with a de Bruijn level.
pub(all) enum Name {
  Global(String)
  Local(Int)
  Quote(Int)
} derive(Show, Eq)

///|
/// Checkable term in dependent type theory that can be type-checked against a
/// given type.
///
/// Constructors:
///
/// * `Inf(TermInf)` : Embedding of an inferable term into a checkable term.
/// * `UnitElement` : The unique element of the unit type.
/// * `Lam(TermChk)` : Lambda abstraction with a body that binds one variable.
/// * `Pair(TermChk, TermChk)` : Ordered pair containing two checkable terms.
/// * `Rfl(TermChk)` : Reflexivity proof for identity types, proving that a term
///   equals itself.
/// * `Sup(TermChk, TermChk)` : Constructor for W-types (well-founded trees)
///   with shape and children components.
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
/// Inferrable terms in type theory that synthesize their types during type
/// checking.
///
/// Constructors:
///
/// * `Bound(Int)` : De Bruijn index for bound variables
/// * `Free(Name)` : Free variable with a name
/// * `UnitType` : The unit type ()
/// * `Universe(Int)` : Type universe at the given level
/// * `Ann(TermChk, TermChk)` : Type annotation (term : type)
/// * `Pi(TermChk, TermChk)` : Dependent function type (x : A) -> B
/// * `App(TermInf, TermChk)` : Function application
/// * `Sigma(TermChk, TermChk)` : Dependent pair type (x : A) × B
/// * `Fst(TermInf)` : First projection of a pair
/// * `Snd(TermInf)` : Second projection of a pair
/// * `Id(TermChk, TermChk, TermChk)` : Identity type Id(A, x, y)
/// * `JElim(TermChk, TermChk, TermChk, TermChk, TermChk, TermInf)` : J
///   eliminator for identity types
/// * `W(TermChk, TermChk)` : Well-founded tree type W(A, B)
/// * `WRec(TermChk, TermChk, TermChk, TermChk, TermInf)` : Recursion principle
///   for W-types
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
/// Neutral value in the type theory system that represents terms that cannot be
/// further reduced during evaluation.
///
/// Neutral values arise when evaluation is blocked by free variables or when we
/// encounter eliminators applied to neutral terms. They maintain the structure
/// needed for later substitution when the blocking variables become known.
///
/// Constructors:
///
/// * `NFree(Name)` - Free variable that blocks further evaluation
/// * `NApp(Neutral, Value)` - Function application where the function is
///   neutral
/// * `NFst(Neutral)` - First projection of a neutral pair
/// * `NSnd(Neutral)` - Second projection of a neutral pair
/// * `NJElim(Value, Value, Value, Value, Value, Neutral)` - Identity type
///   eliminator (J rule) applied to a neutral proof term
/// * `NWRec(Value, (Value) -> Value, Value, Value, Neutral)` - W-type recursion
///   eliminator applied to a neutral W-type value
pub(all) enum Neutral {
  NFree(Name)
  NApp(Neutral, Value)
  NFst(Neutral)
  NSnd(Neutral)
  NJElim(Value, Value, Value, Value, Value, Neutral)
  NWRec(Value, (Value) -> Value, Value, Value, Neutral)
} derive(Show)

///|
/// Runtime values in the type system representing fully evaluated terms.
///
/// Constructors:
///
/// * `VNeutral(Neutral)` : Neutral value that cannot be reduced further
/// * `VUnitType` : The unit type
/// * `VUnitElement` : The unit value
/// * `VUniverse(Int)` : Universe at the given level
/// * `VLam((Value) -> Value)` : Lambda function with closure
/// * `VPi(Value, (Value) -> Value)` : Pi type (dependent function type) with
///   domain and codomain function
/// * `VSigma(Value, (Value) -> Value)` : Sigma type (dependent pair type) with
///   first component type and second component type function
/// * `VPair(Value, Value)` : Pair value with first and second components
/// * `VId(Value, Value, Value)` : Identity type with type, left endpoint, and
///   right endpoint
/// * `VRfl(Value)` : Reflexivity proof for identity type
/// * `VW(Value, (Value) -> Value)` : W-type (well-founded tree type) with label
///   type and child type function
/// * `VSup(Value, (Value) -> Value)` : Constructor for W-type with label and
///   children function
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

pub type Type = Value

///|
/// Mapping from variable names to their types in a type-checking environment.
pub type Context = @list.List[(Name, Type)]
