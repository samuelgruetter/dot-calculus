package miniscala

import scala.collection.immutable.Seq

object LocallyNamelessDotTrees {

  sealed trait Vr
  case class VarF(i: Int, origName: String) extends Vr
  case class VarB(i: Int, origName: String) extends Vr
  case class VObj(ds: Seq[Dm], origSelfName: String) extends Vr

  sealed trait Ty
  case object TBot extends Ty
  case object TTop extends Ty
  case class TFun(name: Int, argType: Ty, retType: Ty, origName: String, origArgName: String) extends Ty
  case class TMem(name: Int, lo: Ty, hi: Ty, origName: String) extends Ty
  case class TAlias(name: Int, tp: Ty, origName: String) extends Ty // syntactic sugar defined in DOT
  case class TSel(qual: Vr, sel: Int, origSel: String) extends Ty
  case class TBind(tp: Ty, origSelfName: String) extends Ty
  case class TAnd(tp1: Ty, tp2: Ty) extends Ty
  case class TOr(tp1: Ty, tp2: Ty) extends Ty

  sealed trait Tm
  case class TmVar(v: Vr) extends Tm
  case class TmApp(t1: Tm, l: Int, t2: Tm, origLabel: String) extends Tm

  sealed trait Dm
  case class DFun(argType: Ty, retType: Ty, body: Tm, origName: String, origArgName: String) extends Dm
  case class DTy(tp: Ty, origName: String) extends Dm
  case object DNone extends Dm

}
