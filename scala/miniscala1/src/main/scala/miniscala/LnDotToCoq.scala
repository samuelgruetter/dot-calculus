package miniscala

import miniscala.LocallyNamelessDotTrees._

import scala.collection.immutable.Seq

object LnDotToCoq {

  private var nIndent: Int = 0
  private def indent: String = List.fill(nIndent)("  ").mkString("")
  private def indented(op: => String): String = {
    nIndent += 1
    val res = op
    nIndent -= 1
    res
  }
  
  def printTm(t: Tm): String = ensureBalanced(t match {
    case TmVar(v) => s"(tvar ${printVr(v)})"
    case TmApp(receiver, label, arg, origLabel) => s"(tapp ${printTm(receiver)} $label (*$origLabel*) ${printTm(arg)})"
  })

  def printVr(v: Vr): String = ensureBalanced(v match {
    case VarF(i, origName) => s"(VarF $i (*$origName*))"
    case VarB(i, origName) => s"(VarB $i (*$origName*))"
    case VObj(Seq(), _) => s"(VObj dnil)"
    case VObj(ds, origSelfName) =>
      s"""(VObj ${origSelfNameComment(origSelfName)}
         |$indent  ${indented(printDms(ds))}
         |$indent)""".stripMargin
  })

  def printTy(tp: Ty): String = ensureBalanced(tp match {
    case TBot => "TBot"
    case TTop => "TTop"
    case TFun(name, argType, retType, origName, origArgName) =>
      s"(TFun $name (*$origName*) (*$origArgName*) ${printTy(argType)} ${printTy(retType)})"
    case TMem(name, lo, hi, origName) =>
      s"(TMem $name (*$origName*) ${printTy(lo)} ${printTy(hi)})"
    case TAlias(name, tp, origName) =>
      s"(TAlias $name (*$origName*) ${printTy(tp)})"
    case TSel(qual, sel, origSel) =>
      s"(TSel ${printVr(qual)} $sel (*$origSel*))"
    case TBind(tp, origSelfName) =>
      s"""(TBind ${origSelfNameComment(origSelfName)}
         |$indent  ${indented(printTy(tp))}
         |$indent)""".stripMargin
    case TAnd(tp1, tp2) =>
      s"""(TAnd ${printTy(tp1)}
         |$indent${printTy(tp2)})""".stripMargin
    case TOr(tp1, tp2) => s"(TOr ${printTy(tp1)} ${printTy(tp2)})"
  })

  def printDm(d: Dm): String = ensureBalanced(d match {
    case DFun(argType, retType, body, origName, origArgName) =>
      s"""(dfun (*$origName*) (*$origArgName*) ${printTy(argType)} ${printTy(retType)} ${printTm(body)})"""
    case DTy(tp, origName) => s"(dty (*$origName*) ${printTy(tp)})"
    case DNone => s"dnone"
  })

  def printDms(ds: Seq[Dm]): String = ensureBalanced(if (ds.isEmpty) {
    "dnil"
  } else {
    s"""(dcons ${printDm(ds.head)}
        |$indent${printDms(ds.tail)})""".stripMargin
  })

  def origSelfNameComment(n: String) = if (n.isEmpty) "" else s"(*$n =>*)"

  def ensureBalanced(s: String): String = {
    var d = 0
    for (c <- s) c match {
      case '(' => d += 1
      case ')' => if (d == 0) sys.error("Not balanced: " + s) else d -= 1
      case _ => // NOP
    }
    if (d != 0) sys.error("Not balanced: " + s)
    s
  }

}
