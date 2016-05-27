package miniscala

import miniscala.LocallyNamelessMiniScalaTrees._

object LnMiniscalaToCoq {

  private var nIndent: Int = 0
  private def indent: String = List.fill(nIndent)("  ").mkString("")
  private def indented(op: => String): String = {
    nIndent += 1
    val res = op
    nIndent -= 1
    res
  }

  def printVr(v: Vr): String = v match {
    case VrFree(i, origName) => s"(VarFr $i (*$origName*))"
    case VrBound(i, origName) => s"(VarBd $i (*$origName*))"
  }

  def printPth(p: Pth): String = p match {
    case PthVar(v) => s"(PthVar ${printVr(v)})"
    case PthSel(prefix, sel, origSel) => s"(PthSel ${printVr(prefix)} $sel (*$origSel*))"
  }

  def printTrm(t: Trm): String = t match {
    case Var(v) => s"(TrmVar ${printVr(v)})"
    case App(receiver, label, arg, origLabel) => s"(TrmApp ${printTrm(receiver)} $label (*$origLabel*) ${printTrm(arg)})"
    case New(cls) => s"(TrmNew ${printPth(cls)})"
    case Block(stat, expr) =>
      s"""(TrmBlock
         |$indent  ${indented(printDef(stat))}
         |$indent  ${indented(printTrm(expr))}
         |$indent)""".stripMargin
  }

  def printDef(d: Def): String = d match {
    case DefVal(typ, rhs, origLabel) => s"(DefVal (*$origLabel*) ${printTyp(typ)} ${printTrm(rhs)})"
    case DefDef(argTyp, retTyp, body, origLabel, origArgName) =>
      s"""(DefDef (*$origLabel*) (*$origArgName*) ${printTyp(argTyp)} ${printTyp(retTyp)} ${printTrm(body)})"""
    case DefClass(defs, origLabel, origSelfName) =>
      s"""(DefCls (*$origLabel*) ${origSelfNameComment(origSelfName)}
         |$indent  ${indented(printDefs(defs))}
         |$indent)""".stripMargin
    case DefNone => "DefNone"
  }

  def printDefs(defs: Seq[Def]): String = if (defs.isEmpty) {
    "DefsNil"
  } else {
    s"""(DefsCons ${printDef(defs.head)}
       |$indent${printDefs(defs.tail)})""".stripMargin
  }

  def printTyp(t: Typ): String = t match {
    case TypCls(ref) => s"(TypCls ${printPth(ref)})"
    case TypMtd(argTyp, retTyp, origArgName) => s"(TypMtd (*$origArgName*) ${printTyp(argTyp)} ${printTyp(retTyp)})"
    case TypOfCls(members, origSelfName) => s"(TypOfCls ${origSelfNameComment(origSelfName)} ${indented(printDefs(members))})"
  }

  def origSelfNameComment(n: String) = if (n.isEmpty) "" else s"(*$n =>*)"

}
