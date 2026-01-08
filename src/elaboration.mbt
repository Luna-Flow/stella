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
pub fn v_j_elim(
  a : Value,
  x : Value,
  motive : Value,
  base_case : Value,
  y : Value,
  p : Value,
) -> Value {
  match p {
    VRfl(_) => base_case
    VNeutral(n) => VNeutral(NJElim(a, x, motive, base_case, y, n))
    _ => panic()
  }
}

///|
pub fn v_w_rec(
  a : Value,
  b : (Value) -> Value,
  mot : Value,
  step : Value,
  target : Value,
) -> Value {
  match target {
    VSup(s, f) => {
      let ih = VLam(fn(p) { v_w_rec(a, b, mot, step, f(p)) })
      v_app(v_app(v_app(step, s), VLam(f)), ih)
    }
    VNeutral(n) => VNeutral(NWRec(a, b, mot, step, n))
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
    UnitType => VUnitType
    Id(a, x, y) => VId(eval_chk(a, d), eval_chk(x, d), eval_chk(y, d))
    JElim(a, x, mot, base, y, p) =>
      v_j_elim(
        eval_chk(a, d),
        eval_chk(x, d),
        eval_chk(mot, d),
        eval_chk(base, d),
        eval_chk(y, d),
        eval_inf(p, d),
      )
    W(a, b) => VW(eval_chk(a, d), fn(x) { eval_chk(b, cons(x, d)) })
    WRec(a, b, mot, step, target) => {
      let va = eval_chk(a, d)
      let vb = fn(x) { eval_chk(b, cons(x, d)) }
      v_w_rec(va, vb, eval_chk(mot, d), eval_chk(step, d), eval_inf(target, d))
    }
  }
}

///|
pub fn eval_chk(t : TermChk, d : Env) -> Value {
  match t {
    Inf(i) => eval_inf(i, d)
    Lam(e) => VLam(x => eval_chk(e, cons(x, d)))
    Pair(x, y) => VPair(eval_chk(x, d), eval_chk(y, d))
    UnitElement => VUnitElement
    Rfl(x) => VRfl(eval_chk(x, d))
    Sup(s, f) => {
      let vs = eval_chk(s, d)
      let vf = eval_chk(f, d)
      match vf {
        VLam(cl) => VSup(vs, cl)
        VNeutral(n) => VSup(vs, fn(v) { v_app(VNeutral(n), v) })
        _ => panic()
      }
    }
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
    UnitType => UnitType
    Id(a, x, y) =>
      Id(subst_chk(i, r, a), subst_chk(i, r, x), subst_chk(i, r, y))
    JElim(a, x, mot, met, y, p) =>
      JElim(
        subst_chk(i, r, a),
        subst_chk(i, r, x),
        subst_chk(i, r, mot),
        subst_chk(i, r, met),
        subst_chk(i, r, y),
        subst_inf(i, r, p),
      )
    W(a, b) => W(subst_chk(i, r, a), subst_chk(i + 1, r, b))
    WRec(a, b, mot, step, target) =>
      WRec(
        subst_chk(i, r, a),
        subst_chk(i, r, b),
        subst_chk(i, r, mot),
        subst_chk(i, r, step),
        subst_inf(i, r, target),
      )
  }
}

///|
pub fn subst_chk(i : Int, r : TermInf, t : TermChk) -> TermChk {
  match t {
    Inf(e) => Inf(subst_inf(i, r, e))
    Lam(e) => Lam(subst_chk(i + 1, r, e))
    Pair(x, y) => Pair(subst_chk(i, r, x), subst_chk(i, r, y))
    UnitElement => UnitElement
    Rfl(x) => Rfl(subst_chk(i, r, x))
    Sup(s, f) => Sup(subst_chk(i, r, s), subst_chk(i, r, f))
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
    VUnitType => Inf(UnitType)
    VUnitElement => UnitElement
    VId(a, x, y) => Inf(Id(quote(i, a), quote(i, x), quote(i, y)))
    VRfl(x) => Rfl(quote(i, x))
    VW(a, b) => Inf(W(quote(i, a), quote(i + 1, b(v_free(Quote(i))))))
    VSup(s, f) => Sup(quote(i, s), Lam(quote(i + 1, f(v_free(Quote(i))))))
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
    NJElim(a, x, mot, base, y, p) =>
      JElim(
        quote(i, a),
        quote(i, x),
        quote(i, mot),
        quote(i, base),
        quote(i, y),
        neutral_quote(i, p),
      )
    NWRec(a, b, mot, step, n) =>
      WRec(
        quote(i, a),
        quote(i + 1, b(v_free(Quote(i)))),
        quote(i, mot),
        quote(i, step),
        neutral_quote(i, n),
      )
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
    UnitType => VStar
    Id(a, x, y) => {
      type_chk(i, g, a, VStar)
      let va = eval_chk(a, empty())
      type_chk(i, g, x, va)
      type_chk(i, g, y, va)
      VStar
    }
    JElim(a, x, mot, base, y, p) => {
      type_chk(i, g, a, VStar)
      let va = eval_chk(a, empty())
      type_chk(i, g, x, va)
      let vx = eval_chk(x, empty())
      type_chk(i, g, y, va)
      let vy = eval_chk(y, empty())
      type_chk(i, g, Inf(p), VId(va, vx, vy))
      let vp = eval_inf(p, empty())
      let mot_ty = VPi(va, fn(y_p) { VPi(VId(va, vx, y_p), fn(_) { VStar }) })
      type_chk(i, g, mot, mot_ty)
      let v_mot = eval_chk(mot, empty())
      let base_ty = v_app(v_app(v_mot, vx), VRfl(vx))
      type_chk(i, g, base, base_ty)
      v_app(v_app(v_mot, vy), vp)
    }
    WRec(a, b, mot, step, target) => {
      type_chk(i, g, a, VStar)
      let va = eval_chk(a, empty())
      type_chk(i, g, b, VPi(va, fn(_) { VStar }))
      let vb_val = eval_chk(b, empty())
      let vb = match vb_val {
        VPi(_, f) => f
        _ => raise TypeError("W position must be a Pi")
      }
      let v_w = VW(va, vb)
      type_chk(i, g, Inf(target), v_w)
      let v_target = eval_inf(target, empty())
      type_chk(i, g, mot, VPi(v_w, fn(_) { VStar }))
      let v_mot = eval_chk(mot, empty())
      let step_ty = VPi(va, fn(s) {
        let v_bs = vb(s)
        let v_f_ty = VPi(v_bs, fn(_) { v_w })
        VPi(v_f_ty, fn(f) {
          let v_ih_ty = VPi(v_bs, fn(p) { v_app(v_mot, v_app(f, p)) })
          VPi(v_ih_ty, fn(_) {
            let f_closure = fn(pos) { v_app(f, pos) }
            v_app(v_mot, VSup(s, f_closure))
          })
        })
      })
      type_chk(i, g, step, step_ty)
      v_app(v_mot, v_target)
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
    UnitElement =>
      match v {
        VUnitType => ()
        _ => raise TypeError("Type Mismatch")
      }
    Rfl(x) =>
      match v {
        VId(va, vx, vy) => {
          type_chk(i, g, x, va)
          let v_x = eval_chk(x, empty())
          if quote(i, v_x) != quote(i, vx) || quote(i, v_x) != quote(i, vy) {
            raise TypeError("Rfl endpoint mismatch")
          }
        }
        _ => raise TypeError("Type Mismatch")
      }
    Sup(s, f) =>
      match v {
        VW(va, vb) => {
          type_chk(i, g, s, va)
          let vs = eval_chk(s, empty())
          let v_bs = vb(vs)
          type_chk(i, g, f, VPi(v_bs, fn(_pos) { VW(va, vb) }))
        }
        _ => raise TypeError("Type Mismatch: Expected W-type for Sup")
      }
  }
}

///|
pub fn type_inf_0(g : Context, t : TermInf) -> Type raise TypeError {
  type_inf(0, g, t)
}
