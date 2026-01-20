///|
using @list {cons, empty}

///|
pub type Env = @list.List[Value]

///|
pub suberror TypeError {
  TypeError(String)
}

///|
pub fn val_var(n : Name) -> Value {
  VNeutral(NFree(n))
}

///|
pub fn val_app(func : Value, arg : Value) -> Value {
  match func {
    VLam(f) => f(arg)
    VNeutral(neu) => VNeutral(NApp(neu, arg))
    _ => panic()
  }
}

///|
pub fn val_fst(val : Value) -> Value {
  match val {
    VPair(a, _) => a
    VNeutral(neu) => VNeutral(NFst(neu))
    _ => panic()
  }
}

///|
pub fn val_snd(val : Value) -> Value {
  match val {
    VPair(_, b) => b
    VNeutral(neu) => VNeutral(NSnd(neu))
    _ => panic()
  }
}

///|
pub fn val_j_elim(
  type_a : Value,
  val_x : Value,
  motive : Value,
  base : Value,
  val_y : Value,
  eq_proof : Value,
) -> Value {
  match eq_proof {
    VRfl(_) => base
    VNeutral(neu) => VNeutral(NJElim(type_a, val_x, motive, base, val_y, neu))
    _ => panic()
  }
}

///|
pub fn val_w_rec(
  type_a : Value,
  type_b : (Value) -> Value,
  motive : Value,
  step : Value,
  target : Value,
) -> Value {
  match target {
    VSup(s, f) => {
      let ih = VLam(fn(pos) { val_w_rec(type_a, type_b, motive, step, f(pos)) })
      val_app(val_app(val_app(step, s), VLam(f)), ih)
    }
    VNeutral(neu) => VNeutral(NWRec(type_a, type_b, motive, step, neu))
    _ => panic()
  }
}

///|
pub fn val_max_univ(val1 : Value, val2 : Value) -> Value {
  match (val1, val2) {
    (VUniverse(u1), VUniverse(u2)) => VUniverse(u1.max(u2))
    _ => panic()
  }
}

///|
fn ensure_inf(
  lvl : Int,
  ctx : Context,
  env : Env,
  term_chk : TermChk,
) -> Value raise TypeError {
  guard term_chk is Inf(term_inf) else { raise TypeError("Type must be Inf") }
  type_inf(lvl, ctx, env, term_inf)
}

///|
fn ensure_univ(val : Value) -> Int raise TypeError {
  match val {
    VUniverse(univ_lvl) => univ_lvl
    _ => raise TypeError("Expected a universe")
  }
}

///|
fn infer_neutral_type(ctx : Context, neu : Neutral) -> Type? {
  match neu {
    NFree(x) =>
      match ctx.iter().find_first(fn(pair) { pair.0 == x }) {
        Some((_, ty)) => Some(ty)
        None => None
      }
    NApp(n, arg) =>
      match infer_neutral_type(ctx, n) {
        Some(VPi(_, cod)) => Some(cod(arg))
        _ => None
      }
    NFst(n) =>
      match infer_neutral_type(ctx, n) {
        Some(VSigma(dom, _)) => Some(dom)
        _ => None
      }
    NSnd(n) =>
      match infer_neutral_type(ctx, n) {
        Some(VSigma(_, cod)) => Some(cod(val_fst(VNeutral(n))))
        _ => None
      }
    NJElim(_, _, motive, _, val_y, p) =>
      Some(val_app(val_app(motive, val_y), VNeutral(p)))
    NWRec(_, _, motive, _, n) => Some(val_app(motive, VNeutral(n)))
  }
}

///|
fn conv_neu(lvl : Int, ctx : Context, n1 : Neutral, n2 : Neutral) -> Bool {
  match (n1, n2) {
    (NFree(x1), NFree(x2)) => x1 == x2
    (NApp(f1, a1), NApp(f2, a2)) =>
      match infer_neutral_type(ctx, f1) {
        Some(VPi(dom, _)) => {
          if not(conv_neu(lvl, ctx, f1, f2)) {
            return false
          }
          conv_nf(lvl, ctx, a1, a2, dom)
        }
        _ => false
      }
    (NFst(p1), NFst(p2)) =>
      match infer_neutral_type(ctx, p1) {
        Some(VSigma(_, _)) => conv_neu(lvl, ctx, p1, p2)
        _ => false
      }
    (NSnd(p1), NSnd(p2)) =>
      match infer_neutral_type(ctx, p1) {
        Some(VSigma(_, _)) => conv_neu(lvl, ctx, p1, p2)
        _ => false
      }
    _ => neutral_quote(lvl, n1) == neutral_quote(lvl, n2)
  }
}

///|
fn conv_nf(
  lvl : Int,
  ctx : Context,
  val1 : Value,
  val2 : Value,
  ty : Value,
) -> Bool {
  match ty {
    VUniverse(_) => conv_type(lvl, ctx, val1, val2)
    VPi(dom, cod) => {
      let fresh = val_var(Local(lvl))
      let ctx1 = cons((Local(lvl), dom), ctx)
      conv_nf(
        lvl + 1,
        ctx1,
        val_app(val1, fresh),
        val_app(val2, fresh),
        cod(fresh),
      )
    }
    VSigma(dom, cod) => {
      let fst1 = val_fst(val1)
      let fst2 = val_fst(val2)
      if not(conv_nf(lvl, ctx, fst1, fst2, dom)) {
        return false
      }
      conv_nf(lvl, ctx, val_snd(val1), val_snd(val2), cod(fst1))
    }
    VUnitType => true
    _ =>
      match (val1, val2) {
        (VNeutral(n1), VNeutral(n2)) => conv_neu(lvl, ctx, n1, n2)
        _ => quote(lvl, val1) == quote(lvl, val2)
      }
  }
}

///|
fn conv_type(lvl : Int, ctx : Context, val1 : Value, val2 : Value) -> Bool {
  match (val1, val2) {
    (VUniverse(u1), VUniverse(u2)) => u1 == u2
    (VPi(a1, b1), VPi(a2, b2)) => {
      if not(conv_type(lvl, ctx, a1, a2)) {
        return false
      }
      let fresh = val_var(Local(lvl))
      let ctx1 = cons((Local(lvl), a1), ctx)
      conv_type(lvl + 1, ctx1, b1(fresh), b2(fresh))
    }
    (VSigma(a1, b1), VSigma(a2, b2)) => {
      if not(conv_type(lvl, ctx, a1, a2)) {
        return false
      }
      let fresh = val_var(Local(lvl))
      let ctx1 = cons((Local(lvl), a1), ctx)
      conv_type(lvl + 1, ctx1, b1(fresh), b2(fresh))
    }
    (VUnitType, VUnitType) => true
    (VId(a1, x1, y1), VId(a2, x2, y2)) => {
      if not(conv_type(lvl, ctx, a1, a2)) {
        return false
      }
      if not(conv_nf(lvl, ctx, x1, x2, a1)) {
        return false
      }
      conv_nf(lvl, ctx, y1, y2, a1)
    }
    (VW(a1, b1), VW(a2, b2)) => {
      if not(conv_type(lvl, ctx, a1, a2)) {
        return false
      }
      let fresh = val_var(Local(lvl))
      let ctx1 = cons((Local(lvl), a1), ctx)
      conv_type(lvl + 1, ctx1, b1(fresh), b2(fresh))
    }
    (VNeutral(n1), VNeutral(n2)) => conv_neu(lvl, ctx, n1, n2)
    _ => quote(lvl, val1) == quote(lvl, val2)
  }
}

///|
fn subtype_nf(lvl : Int, ctx : Context, val1 : Value, val2 : Value) -> Bool {
  match (val1, val2) {
    (VUniverse(u1), VUniverse(u2)) => u1 <= u2
    (VPi(a1, b1), VPi(a2, b2)) => {
      if not(subtype_nf(lvl, ctx, a2, a1)) {
        return false
      }
      let fresh = val_var(Local(lvl))
      let ctx1 = cons((Local(lvl), a2), ctx)
      subtype_nf(lvl + 1, ctx1, b1(fresh), b2(fresh))
    }
    (VSigma(a1, b1), VSigma(a2, b2)) => {
      if not(conv_type(lvl, ctx, a1, a2)) {
        return false
      }
      let fresh = val_var(Local(lvl))
      let ctx1 = cons((Local(lvl), a1), ctx)
      subtype_nf(lvl + 1, ctx1, b1(fresh), b2(fresh))
    }
    _ => conv_type(lvl, ctx, val1, val2)
  }
}

///|
fn subtype(lvl : Int, ctx : Context, val1 : Value, val2 : Value) -> Bool {
  subtype_nf(lvl, ctx, val1, val2)
}

///|
pub fn def_eq(lvl : Int, val1 : Value, val2 : Value) -> Bool {
  subtype(lvl, empty(), val1, val2)
}

///|
pub fn eval_inf(term : TermInf, env : Env) -> Value {
  match term {
    Bound(idx) => env.iter().nth(idx).unwrap()
    Free(x) => val_var(x)
    UnitType => VUnitType
    Universe(univ_lvl) => VUniverse(univ_lvl)
    Ann(e, _) => eval_chk(e, env)
    Pi(a, b) => VPi(eval_chk(a, env), fn(x) { eval_chk(b, cons(x, env)) })
    App(f, e) => val_app(eval_inf(f, env), eval_chk(e, env))
    Sigma(a, b) => VSigma(eval_chk(a, env), fn(x) { eval_chk(b, cons(x, env)) })
    Fst(p) => val_fst(eval_inf(p, env))
    Snd(p) => val_snd(eval_inf(p, env))
    Id(a, x, y) => VId(eval_chk(a, env), eval_chk(x, env), eval_chk(y, env))
    JElim(a, x, motive, base, y, p) =>
      val_j_elim(
        eval_chk(a, env),
        eval_chk(x, env),
        eval_chk(motive, env),
        eval_chk(base, env),
        eval_chk(y, env),
        eval_inf(p, env),
      )
    W(a, b) => VW(eval_chk(a, env), fn(x) { eval_chk(b, cons(x, env)) })
    WRec(a, b, motive, step, target) => {
      let type_a = eval_chk(a, env)
      let type_b_val = eval_chk(b, env)
      let type_b = fn(v) { val_app(type_b_val, v) }
      val_w_rec(
        type_a,
        type_b,
        eval_chk(motive, env),
        eval_chk(step, env),
        eval_inf(target, env),
      )
    }
  }
}

///|
pub fn eval_chk(term : TermChk, env : Env) -> Value {
  match term {
    Inf(i) => eval_inf(i, env)
    UnitElement => VUnitElement
    Lam(e) => VLam(fn(x) { eval_chk(e, cons(x, env)) })
    Pair(x, y) => VPair(eval_chk(x, env), eval_chk(y, env))
    Rfl(x) => VRfl(eval_chk(x, env))
    Sup(s, f) => {
      let val_s = eval_chk(s, env)
      let val_f = eval_chk(f, env)
      match val_f {
        VLam(cl) => VSup(val_s, cl)
        VNeutral(neu) => VSup(val_s, fn(v) { val_app(VNeutral(neu), v) })
        _ => panic()
      }
    }
  }
}

///|
pub fn quote(lvl : Int, val : Value) -> TermChk {
  match val {
    VNeutral(neu) => Inf(neutral_quote(lvl, neu))
    VUnitType => Inf(UnitType)
    VUnitElement => UnitElement
    VUniverse(univ_lvl) => Inf(Universe(univ_lvl))
    VLam(f) => Lam(quote(lvl + 1, f(val_var(Quote(lvl)))))
    VPi(a, b) => Inf(Pi(quote(lvl, a), quote(lvl + 1, b(val_var(Quote(lvl))))))
    VSigma(a, b) =>
      Inf(Sigma(quote(lvl, a), quote(lvl + 1, b(val_var(Quote(lvl))))))
    VPair(a, b) => Pair(quote(lvl, a), quote(lvl, b))
    VId(a, x, y) => Inf(Id(quote(lvl, a), quote(lvl, x), quote(lvl, y)))
    VRfl(x) => Rfl(quote(lvl, x))
    VW(a, b) => Inf(W(quote(lvl, a), quote(lvl + 1, b(val_var(Quote(lvl))))))
    VSup(s, f) =>
      Sup(quote(lvl, s), Lam(quote(lvl + 1, f(val_var(Quote(lvl))))))
  }
}

///|
pub fn neutral_quote(lvl : Int, neu : Neutral) -> TermInf {
  match neu {
    NFree(x) =>
      match x {
        Quote(k) => Bound(lvl - k - 1)
        _ => Free(x)
      }
    NApp(n, v) => App(neutral_quote(lvl, n), quote(lvl, v))
    NFst(n) => Fst(neutral_quote(lvl, n))
    NSnd(n) => Snd(neutral_quote(lvl, n))
    NJElim(a, x, motive, base, y, p) =>
      JElim(
        quote(lvl, a),
        quote(lvl, x),
        quote(lvl, motive),
        quote(lvl, base),
        quote(lvl, y),
        neutral_quote(lvl, p),
      )
    NWRec(a, b, motive, step, n) =>
      WRec(
        quote(lvl, a),
        quote(lvl + 1, b(val_var(Quote(lvl)))),
        quote(lvl, motive),
        quote(lvl, step),
        neutral_quote(lvl, n),
      )
  }
}

///|
pub fn type_inf(
  lvl : Int,
  ctx : Context,
  env : Env,
  term : TermInf,
) -> Type raise TypeError {
  match term {
    Bound(idx) => {
      let val = env.iter().nth(idx).unwrap()
      match val {
        VNeutral(NFree(n)) =>
          match ctx.iter().find_first(fn(pair) { pair.0 == n }) {
            Some((_, ty)) => ty
            None => raise TypeError("Unknown Identifier")
          }
        _ =>
          raise TypeError("Internal error: Bound variable not in environment")
      }
    }
    Free(x) =>
      match ctx.iter().find_first(fn(pair) { pair.0 == x }) {
        Some((_, ty)) => ty
        None => raise TypeError("Unknown Identifier: \{x}")
      }
    UnitType => VUniverse(0)
    Universe(univ_lvl) => VUniverse(univ_lvl + 1)
    Ann(e, dt) => {
      guard dt is Inf(term_inf) else { raise TypeError("Type must be Inf") }
      let type_of_type = type_inf(lvl, ctx, env, term_inf)
      match type_of_type {
        VUniverse(_) => {
          let ty = eval_inf(term_inf, env)
          type_chk(lvl, ctx, env, e, ty)
          ty
        }
        _ => raise TypeError("The annotation's type is not a type")
      }
    }
    Pi(a, b) | Sigma(a, b) | W(a, b) => {
      let u1 = ensure_inf(lvl, ctx, env, a) |> ensure_univ()
      let type_a = eval_chk(a, env)
      let u2 = ensure_inf(
          lvl + 1,
          cons((Local(lvl), type_a), ctx),
          cons(val_var(Local(lvl)), env),
          b,
        )
        |> ensure_univ()
      VUniverse(u1.max(u2))
    }
    App(f, e) =>
      match type_inf(lvl, ctx, env, f) {
        VPi(a, b) => {
          type_chk(lvl, ctx, env, e, a)
          b(eval_chk(e, env))
        }
        _ => raise TypeError("Illegal Application")
      }
    Fst(p) =>
      match type_inf(lvl, ctx, env, p) {
        VSigma(a, _) => a
        _ => raise TypeError("Fst expects Sigma")
      }
    Snd(p) =>
      match type_inf(lvl, ctx, env, p) {
        VSigma(_, b) => b(val_fst(eval_inf(p, env)))
        _ => raise TypeError("Snd expects Sigma")
      }
    Id(a, x, y) => {
      let univ_lvl = ensure_inf(lvl, ctx, env, a) |> ensure_univ()
      let type_a = eval_chk(a, env)
      type_chk(lvl, ctx, env, x, type_a)
      type_chk(lvl, ctx, env, y, type_a)
      VUniverse(univ_lvl)
    }
    JElim(a, x, motive, base, y, p) => {
      ensure_inf(lvl, ctx, env, a) |> ensure_univ() |> ignore
      let type_a = eval_chk(a, env)
      type_chk(lvl, ctx, env, x, type_a)
      let val_x = eval_chk(x, env)
      type_chk(lvl, ctx, env, y, type_a)
      let val_y = eval_chk(y, env)
      type_chk(lvl, ctx, env, Inf(p), VId(type_a, val_x, val_y))
      let type_motive = ensure_inf(lvl, ctx, env, motive)
      match type_motive {
        VPi(_, f1) =>
          match f1(val_var(Quote(lvl))) {
            VPi(_, f2) => {
              let co_domain = f2(val_var(Quote(lvl + 1)))
              ensure_univ(co_domain) |> ignore
            }
            _ => raise TypeError("Motive must be a binary function")
          }
        _ => raise TypeError("Motive must be a function")
      }
      let val_motive = eval_chk(motive, env)
      type_chk(
        lvl,
        ctx,
        env,
        base,
        val_app(val_app(val_motive, val_x), VRfl(val_x)),
      )
      val_app(val_app(val_motive, val_y), eval_inf(p, env))
    }
    WRec(a, b, motive, step, target) => {
      ensure_inf(lvl, ctx, env, a) |> ensure_univ() |> ignore
      let type_a = eval_chk(a, env)
      let type_b_type = ensure_inf(lvl, ctx, env, b)
      match type_b_type {
        VPi(dom, cod) => {
          if quote(lvl, dom) != quote(lvl, type_a) {
            raise TypeError("W-type: B domain mismatch")
          }
          let _ = ensure_univ(cod(val_var(Quote(lvl))))

        }
        _ => raise TypeError("WRec: B must be a function")
      }
      let type_b_val = eval_chk(b, env)
      let type_b = fn(v) { val_app(type_b_val, v) }
      let type_w = VW(type_a, type_b)
      type_chk(lvl, ctx, env, Inf(target), type_w)
      let type_motive = ensure_inf(lvl, ctx, env, motive)
      match type_motive {
        VPi(dom, cod) => {
          if quote(lvl, dom) != quote(lvl, type_w) {
            raise TypeError("WRec: motive domain mismatch")
          }
          ensure_univ(cod(val_var(Quote(lvl)))) |> ignore
        }
        _ => raise TypeError("WRec: motive must be a function")
      }
      let val_motive = eval_chk(motive, env)
      let step_ty = VPi(type_a, fn(s) {
        let val_bs = type_b(s)
        VPi(VPi(val_bs, fn(_) { type_w }), fn(f) {
          VPi(VPi(val_bs, fn(p) { val_app(val_motive, val_app(f, p)) }), fn(_) {
            val_app(val_motive, VSup(s, fn(pos) { val_app(f, pos) }))
          })
        })
      })
      type_chk(lvl, ctx, env, step, step_ty)
      val_app(val_motive, eval_inf(target, env))
    }
  }
}

///|
pub fn type_chk(
  lvl : Int,
  ctx : Context,
  env : Env,
  term : TermChk,
  exp_type : Type,
) -> Unit raise TypeError {
  match term {
    Inf(term_inf) => {
      let inferred_type = type_inf(lvl, ctx, env, term_inf)
      if not(subtype(lvl, ctx, inferred_type, exp_type)) {
        raise TypeError(
          "Type Mismatch: inferred type is not a subtype of expected type",
        )
      }
    }
    Lam(e) =>
      match exp_type {
        VPi(a, b) =>
          type_chk(
            lvl + 1,
            cons((Local(lvl), a), ctx),
            cons(val_var(Local(lvl)), env),
            e,
            b(val_var(Local(lvl))),
          )
        _ => raise TypeError("Expected Pi type for Lambda")
      }
    Pair(tm_fst, tm_snd) =>
      match exp_type {
        VSigma(a, b) => {
          type_chk(lvl, ctx, env, tm_fst, a)
          type_chk(lvl, ctx, env, tm_snd, b(eval_chk(tm_fst, env)))
        }
        _ => raise TypeError("Expected Sigma type for Pair")
      }
    UnitElement =>
      match exp_type {
        VUnitType => ()
        _ => raise TypeError("Expected UnitType")
      }
    Rfl(x) =>
      match exp_type {
        VId(type_a, val_x, val_y) => {
          type_chk(lvl, ctx, env, x, type_a)
          let val_x_computed = eval_chk(x, env)
          if quote(lvl, val_x_computed) != quote(lvl, val_x) ||
            quote(lvl, val_x_computed) != quote(lvl, val_y) {
            raise TypeError("Rfl endpoints mismatch")
          }
        }
        _ => raise TypeError("Expected Id type for Rfl")
      }
    Sup(s, f) =>
      match exp_type {
        VW(type_a, type_b) => {
          type_chk(lvl, ctx, env, s, type_a)
          let val_s = eval_chk(s, env)
          type_chk(
            lvl,
            ctx,
            env,
            f,
            VPi(type_b(val_s), fn(_) { VW(type_a, type_b) }),
          )
        }
        _ => raise TypeError("Expected W type for Sup")
      }
  }
}

///|
pub fn type_inf_0(ctx : Context, term : TermInf) -> Type raise TypeError {
  type_inf(0, ctx, empty(), term)
}
