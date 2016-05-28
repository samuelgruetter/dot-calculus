package miniscala

object DotTrees {

  sealed trait Vr
  case class Var(name: String) extends Vr
  case class VObj(selfName: String, ds: Seq[Dm]) extends Vr

  sealed trait Ty
  case object TBot extends Ty
  case object TTop extends Ty
  case class TFun(name: String, argName: String, argType: Ty, retType: Ty) extends Ty
  case class TMem(name: String, lo: Ty, hi: Ty) extends Ty
  //def TAlias(name: String, tp: Ty) = TMem(name, tp, tp)
  case class TAlias(name: String, tp: Ty) extends Ty // syntactic sugar defined in DOT
  case class TSel(qual: Vr, sel: String) extends Ty
  case class TBind(selfName: String, tp: Ty) extends Ty
  case class TAnd(tp1: Ty, tp2: Ty) extends Ty
  case class TOr(tp1: Ty, tp2: Ty) extends Ty

  sealed trait Tm
  case class TmVar(v: Vr) extends Tm
  case class TmApp(t1: Tm, l: String, t2: Tm) extends Tm

  sealed trait Dm
  case class DFun(name: String, argName: String, argType: Ty, retType: Ty, body: Tm) extends Dm
  case class DTy(name: String, tp: Ty) extends Dm

  def Let(x: String, t1: Tm, tp1: Ty, t2: Tm, tp2: Ty): Tm = {
    TmApp(TmVar(VObj("_unusedSelf", Seq(DFun("call", x, tp1, tp2, t2)))), "call", t1)
  }
}
