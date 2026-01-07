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
pub fn v_fst(v : Value) -> Value {
  match v {
    VPair(a, _) => a
    VNeutral(n) => VNeutral(NFst(n))
    _ => panic()
  }
}

///|
pub fn v_snd(v : Value) -> Value {
  match v {
    VPair(_, b) => b
    VNeutral(n) => VNeutral(NSnd(n))
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
    Sigma(a, b) => VSigma(eval_chk(a, d), fn(x) { eval_chk(b, cons(x, d)) })
    Fst(p) => v_fst(eval_inf(p, d))
    Snd(p) => v_snd(eval_inf(p, d))
  }
}

///|
pub fn eval_chk(t : TermChk, d : Env) -> Value {
  match t {
    Inf(i) => eval_inf(i, d)
    Lam(e) => VLam(x => eval_chk(e, cons(x, d)))
    Pair(x, y) => VPair(eval_chk(x, d), eval_chk(y, d))
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
    Sigma(a, b) => Sigma(subst_chk(i, r, a), subst_chk(i + 1, r, b))
    Fst(p) => Fst(subst_inf(i, r, p))
    Snd(p) => Snd(subst_inf(i, r, p))
  }
}

///|
pub fn subst_chk(i : Int, r : TermInf, t : TermChk) -> TermChk {
  match t {
    Inf(e) => Inf(subst_inf(i, r, e))
    Lam(e) => Lam(subst_chk(i + 1, r, e))
    Pair(x, y) => Pair(subst_chk(i, r, x), subst_chk(i, r, y))
  }
}

///|
pub fn quote(i : Int, v : Value) -> TermChk {
  match v {
    VLam(f) => Lam(quote(i + 1, f(v_free(Quote(i)))))
    VNeutral(n) => Inf(neutral_quote(i, n))
    VStar => Inf(Star)
    VPi(v, f) => Inf(Pi(quote(i, v), quote(i + 1, f(v_free(Quote(i))))))
    VSigma(v, f) => Inf(Sigma(quote(i, v), quote(i + 1, f(v_free(Quote(i))))))
    VPair(a, b) => Pair(quote(i, a), quote(i, b))
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
    NFst(n) => Fst(neutral_quote(i, n))
    NSnd(n) => Snd(neutral_quote(i, n))
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
    Sigma(a, b) => {
      type_chk(i, g, a, VStar)
      let ty_a = eval_chk(a, empty())
      type_chk(
        i + 1,
        cons((Local(i), ty_a), g),
        subst_chk(0, Free(Local(i)), b),
        VStar,
      )
      VStar
    }
    Fst(p) => {
      let p_ty = type_inf(i, g, p)
      match p_ty {
        VSigma(a, _) => a
        _ => raise TypeError("Fst expects a Sigma type")
      }
    }
    Snd(p) => {
      let p_ty = type_inf(i, g, p)
      match p_ty {
        VSigma(_, b_closure) => {
          let p_val = eval_inf(p, empty())
          let first_val = v_fst(p_val)
          b_closure(first_val) // B(fst p)
        }
        _ => raise TypeError("Snd expects a Sigma type")
      }
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
    Pair(e1, e2) =>
      match v {
        VSigma(a, b) => {
          type_chk(i, g, e1, a)
          let v1 = eval_chk(e1, empty())
          type_chk(i, g, e2, b(v1))
        }
        _ => raise TypeError("Type Mismatch")
      }
  }
}

///|
pub fn type_inf_0(g : Context, t : TermInf) -> Type raise TypeError {
  type_inf(0, g, t)
}
