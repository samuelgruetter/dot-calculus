package miniscala

import miniscala.{MiniScalaTrees => ms}
import miniscala.{DotTrees => dot}

object MiniScalaToDot {

  def translateProg(t: ms.Trm): dot.Tm = trTrm(Nil, t)._2

  // Why also typechecking during translation?
  // - enforce nominality
  // - get type T2 in expressions translated to "let x = t1 in t2" for
  //   "(new { def call(x: T1): T2 = t2 }).call(t1)" (DOT requires explicit return type T2)

  type Ctx = List[(String, ms.Typ)]
  def lookupVar(name: String, ctx: Ctx): ms.Typ = ctx.find(_._1 == name) match {
    case Some((_, tp)) => tp
    case None => sys.error(s"$name not found in context\n${ctx.mkString("\n")}")
  }

  def lookupDef(name: String, defs: Seq[ms.Def]): ms.Def = defs.find(_.name == name).get

  def checkConforms(actual: ms.Typ, expected: ms.Typ): Unit = {
    if (actual != expected) sys.error(s"expected $expected but found $actual")
  }

  def lookupClass(p: ms.Pth, ctx: Ctx): ms.TypOfCls = p match {
    case ms.PthVar(name) => lookupVar(name, ctx).asInstanceOf[ms.TypOfCls]
    case ms.PthSel(prefix, sel) =>
      val ms.TypCls(q) = lookupVar(prefix, ctx)
      val ms.TypOfCls(z0, ds0) = lookupClass(q, ctx)
      val ms.DefClass(_, z, ds) = lookupDef(sel, ds0)
      ms.TypOfCls(z, ds.map(_.subst(z0, prefix)))
  }

  val unit = dot.TmVar(dot.VObj("_", Seq()))

  def trTyp(t: ms.Pth): dot.Ty = t match {
    case ms.PthVar(name) => dot.TSel(dot.Var(name), "C")
    case ms.PthSel(prefix, sel) => dot.TSel(dot.Var(prefix), "C_" + sel)
  }

  def trCtorRef(c: ms.Pth): dot.Tm = c match {
    case ms.PthVar(name) => dot.TmApp(dot.TmVar(dot.Var(name)), "new", unit)
    case ms.PthSel(prefix, sel) => dot.TmApp(dot.TmVar(dot.Var(prefix)), "new_" + sel, unit)
  }

  def trTypOfDef(d: ms.Def, outerSelfRef: String): (dot.Ty, dot.Ty) = d match {
    case ms.DefClass(name, selfName, defs) =>
      val defsType = trTypOfDefs(defs, selfName)
      val tpmem = dot.TAlias("C_" + name, dot.TBind(selfName, defsType))
      val defmem = dot.TFun("new_" + name, "_dummy", dot.TTop, dot.TSel(dot.Var(outerSelfRef), "C_" + name))
      (tpmem, defmem)
    case ms.DefDef(name, argName, argTp, retTp, body) =>
      val ms.TypCls(argTpPth) = argTp
      val ms.TypCls(retTpPth) = retTp
      (dot.TFun(name, argName, trTyp(argTpPth), trTyp(retTpPth)), dot.TTop)
    case ms.DefVal(name, tp, rhs) => sys.error("not yet supported")
  }

  def trTypOfDefs(ds: Seq[ms.Def], outerSelfRef: String): dot.Ty = if (ds.isEmpty) {
    dot.TTop
  } else {
    val (t1, t2) = trTypOfDef(ds.head, outerSelfRef)
    dot.TAnd(t1, dot.TAnd(t2, trTypOfDefs(ds.tail, outerSelfRef)))
  }

  // returns Seq of length 1 or 2
  def trDef(ctx: Ctx, d: ms.Def, outerSelfRef: String): Seq[dot.Dm] = d match {
    case ms.DefClass(name, selfName, defs) =>
      val ctx2 = (selfName, ms.TypCls(ms.PthSel(outerSelfRef, name))) :: ctx
      val defsType = trTypOfDefs(defs, selfName)
      val tpdef = dot.DTy("C_" + name, dot.TBind(selfName, defsType))
      val defdef = dot.DFun("new_" + name, "_dummy", dot.TTop, dot.TSel(dot.Var(outerSelfRef), "C_" + name),
        dot.TmVar(dot.VObj(selfName, trDefs(ctx2, defs, selfName)))
      )
      Seq(tpdef, defdef)
    case ms.DefDef(name, argName, argTp, retTp, body) =>
      val (actualRetTp, body2) = trTrm((argName, argTp) :: ctx, body)
      checkConforms(actualRetTp, retTp)
      val ms.TypCls(argTpPth) = argTp
      val ms.TypCls(retTpPth) = retTp
      Seq(dot.DFun(name, argName, trTyp(argTpPth), trTyp(retTpPth), body2))
    case ms.DefVal(name, tp, rhs) => sys.error("not yet supported")
  }

  def trDefs(ctx: Ctx, ds: Seq[ms.Def], outerSelfRef: String): Seq[dot.Dm] = if (ds.isEmpty) {
    Seq()
  } else {
    trDef(ctx, ds.head, outerSelfRef) ++ trDefs(ctx, ds.tail, outerSelfRef)
  }

  def trTrm(ctx: Ctx, t: ms.Trm): (ms.Typ, dot.Tm) = t match {
    case ms.Var(name) => (lookupVar(name, ctx), dot.TmVar(dot.Var(name)))

    // TODO notin FV checks
    case ms.App(ms.Var(x1), label, ms.Var(x2)) =>
      val ms.TypCls(p1) = lookupVar(x1, ctx)
      val ms.TypCls(p2) = lookupVar(x2, ctx)
      val ms.TypOfCls(z, ds) = lookupClass(p1, ctx)
      val ms.DefDef(_, argName, argTyp, retTyp, _) = lookupDef(label, ds).subst(z, x1)
      checkConforms(ms.TypCls(p2), argTyp)
      (retTyp.subst(argName, x2), dot.TmApp(dot.TmVar(dot.Var(x1)), label, dot.TmVar(dot.Var(x2))))
    case ms.App(ms.Var(x1), label, t2) =>
      val ms.TypCls(p1) = lookupVar(x1, ctx)
      val (tp2, t2a) = trTrm(ctx, t2)
      val ms.TypOfCls(z, ds) = lookupClass(p1, ctx)
      val ms.DefDef(_, argName, argTyp, retTyp, _) = lookupDef(label, ds).subst(z, x1)
      checkConforms(tp2, argTyp)
      (retTyp, dot.TmApp(dot.TmVar(dot.Var(x1)), label, t2a))
    case ms.App(t1, label, ms.Var(x2)) =>
      val (ms.TypCls(p1), t1a) = trTrm(ctx, t1)
      val ms.TypCls(p2) = lookupVar(x2, ctx)
      val ms.TypOfCls(z, ds) = lookupClass(p1, ctx)
      val ms.DefDef(_, argName, argTyp, retTyp, _) = lookupDef(label, ds)
      checkConforms(ms.TypCls(p2), argTyp)
      (retTyp.subst(argName, x2), dot.TmApp(t1a, label, dot.TmVar(dot.Var(x2))))
    case ms.App(t1, label, t2) =>
      val (ms.TypCls(p1), t1a) = trTrm(ctx, t1)
      val (tp2, t2a) = trTrm(ctx, t2)
      val ms.TypOfCls(z, ds) = lookupClass(p1, ctx)
      val ms.DefDef(_, argName, argTyp, retTyp, _) = lookupDef(label, ds)
      checkConforms(tp2, argTyp)
      (retTyp, dot.TmApp(t1a, label, t2a))

    case ms.New(cls) =>
      val _ = lookupClass(cls, ctx)
      (ms.TypCls(cls), trCtorRef(cls))

    case ms.Block(ms.DefVal(name, tp1, t1), t2) =>
      val (actualTp1, t1a) = trTrm(ctx, t1)
      checkConforms(actualTp1, tp1)
      val ctx2 = (name, tp1) :: ctx
      val (tp2, t2a) = trTrm(ctx2, t2) // NOTE: here we get the type t2a, that's why we need to do typechecking
      val ms.TypCls(tp1Pth) = tp1
      val ms.TypCls(tp2Pth) = tp2
      (tp2, dot.Let(name, t1a, trTyp(tp1Pth), t2a, trTyp(tp2Pth)))
    case ms.Block(ms.DefClass(name, selfName, defs), t2) =>
      val ctx2 = (name, ms.TypOfCls(selfName, defs)) :: ctx
      val ctx3 = (selfName, ms.TypCls(ms.PthVar(name))) :: ctx2
      val defs2 = trDefs(ctx3, defs, selfName)
      val defsTp = trTypOfDefs(defs, selfName)
      val (tp2, t2a) = trTrm(ctx2, t2)
      val ms.TypCls(tp2Pth) = tp2
      val obj = dot.VObj("_self", Seq(
        dot.DTy("C", dot.TBind(selfName, defsTp)),
        dot.DFun("new", "_dummy", dot.TTop, dot.TSel(dot.Var("_self"), "C"), dot.TmVar(dot.VObj(selfName, defs2)))
      ))
      val objTp = dot.TBind("_self", dot.TAnd(
        dot.TAlias("C", dot.TBind(selfName, defsTp)),
        dot.TFun("new", "_dummy", dot.TTop, dot.TSel(dot.Var("_self"), "C"))
      ))
      (tp2, dot.Let(name, dot.TmVar(obj), objTp, t2a, trTyp(tp2Pth)))
    case ms.Block(ms.DefDef(name, argName, argTyp, retTyp, body), expr) => sys.error("not yet supported")
  }

}
