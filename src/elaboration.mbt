///|
using @list {cons, empty}

///|
pub type Env = @list.List[Value]

///|
pub fn v_free(n : Name) -> Value {
  VNeutral(NFree(n))
}

///|
pub fn v_app(e : Value, v : Value) -> Value {
  match e {
    VLam(f) => f(v)
    VNeutral(n) => VNeutral(NApp(n, v))
    _ => panic()
  }
}

///|
pub fn eval_inf(t : TermInf, d : Env) -> Value {
  match t {
    Ann(e, _) => eval_chk(e, d)
    Free(x) => v_free(x)
    Bound(i) => d.iter().nth(i).unwrap()
    App(f, e) => v_app(eval_inf(f, d), eval_chk(e, d))
    Star => VStar
    Pi(a, b) => VPi(eval_chk(a, d), x => eval_chk(b, cons(x, d)))
  }
}

///|
pub fn eval_chk(t : TermChk, d : Env) -> Value {
  match t {
    Inf(i) => eval_inf(i, d)
    Lam(e) => VLam(x => eval_chk(e, cons(x, d)))
  }
}

///|
pub fn bound_free(i : Int, n : Name) -> TermInf {
  match n {
    Quote(k) => Bound(i - k - 1)
    x => Free(x)
  }
}

///|
pub fn subst_inf(i : Int, r : TermInf, t : TermInf) -> TermInf {
  match t {
    Ann(e_chk, t) => Ann(subst_chk(i, r, e_chk), subst_chk(i, r, t))
    Bound(j) => if i == j { r } else { Bound(j) }
    Free(y) => Free(y)
    App(e, a) => App(subst_inf(i, r, e), subst_chk(i, r, a))
    Star => Star
    Pi(a, b) => Pi(subst_chk(i, r, a), subst_chk(i + 1, r, b))
  }
}

///|
pub fn subst_chk(i : Int, r : TermInf, t : TermChk) -> TermChk {
  match t {
    Inf(e) => Inf(subst_inf(i, r, e))
    Lam(e) => Lam(subst_chk(i + 1, r, e))
  }
}

///|
pub fn quote(i : Int, v : Value) -> TermChk {
  match v {
    VLam(f) => Lam(quote(i + 1, f(v_free(Quote(i)))))
    VNeutral(n) => Inf(neutral_quote(i, n))
    VStar => Inf(Star)
    VPi(v, f) => Inf(Pi(quote(i, v), quote(i + 1, f(v_free(Quote(i))))))
  }
}

///|
pub fn quote_0(v : Value) -> TermChk {
  quote(0, v)
}

///|
pub fn neutral_quote(i : Int, n : Neutral) -> TermInf {
  match n {
    NFree(x) => bound_free(i, x)
    NApp(n, v) => App(neutral_quote(i, n), quote(i, v))
  }
}

///|
pub(all) suberror TypeError String

///|
pub fn type_inf(i : Int, g : Context, t : TermInf) -> Type raise TypeError {
  match t {
    Ann(e, dt) => {
      type_chk(i, g, dt, VStar)
      let ty = eval_chk(dt, empty())
      type_chk(i, g, e, ty)
      ty
    }
    Star => VStar
    Pi(a, b) => {
      type_chk(i, g, a, VStar)
      let ty = eval_chk(a, empty())
      type_chk(
        i + 1,
        cons((Local(i), ty), g),
        subst_chk(0, Free(Local(i)), b),
        VStar,
      )
      VStar
    }
    Free(x) =>
      for nv in g {
        let (n, v) = nv
        if x == n {
          return v
        }
      } else {
        raise TypeError("Unknown Identifier")
      }
    App(f, e) =>
      match type_inf(i, g, f) {
        VPi(a, b) => {
          type_chk(i, g, e, a)
          b(eval_chk(e, empty()))
        }
        _ => raise TypeError("Illegal Application")
      }
    _ => panic()
  }
}

///|
pub fn type_chk(
  i : Int,
  g : Context,
  t : TermChk,
  v : Type,
) -> Unit raise TypeError {
  match t {
    Inf(e) => {
      let vn = type_inf(i, g, e)
      if quote_0(v) != quote_0(vn) {
        raise TypeError("Type Mismatch")
      }
    }
    Lam(e) =>
      match v {
        VPi(a, b) =>
          type_chk(
            i + 1,
            cons((Local(i), a), g),
            subst_chk(0, Free(Local(i)), e),
            b(v_free(Local(i))),
          )
        _ => raise TypeError("Type Mismatch")
      }
  }
}

///|
pub fn type_inf_0(g : Context, t : TermInf) -> Type raise TypeError {
  type_inf(0, g, t)
}
