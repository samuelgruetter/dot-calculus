package miniscala

import miniscala.{DotTrees => dot}
import miniscala.{LocallyNamelessDotTrees => ln}

import scala.collection.immutable.Seq

object DotTreesToLocallyNameless {

  // maps label names (Strings) to their index inside classes
  class LabelTable private (val repr: List[String]) {
    def apply(label: String): Int = {
      val i = repr.indexOf(label)
      if (i < 0) throw new NoSuchElementException(label + " not found")
      i
    }
    def encounter(label: String): LabelTable = {
      val i = repr.indexOf(label)
      if (i < 0) {
        new LabelTable(repr :+ label)
      } else {
        this
      }
    }
    def size: Int = repr.size
  }
  object LabelTable {
    val empty = new LabelTable(Nil)
  }

  // maps names (Strings) to their de Brujin index
  class LnTable private (val repr: List[String]) {
    def apply(name: String): Int = {
      val i = repr.indexOf(name)
      if (i < 0) throw new NoSuchElementException(name + " not found in \n" + repr.zipWithIndex.mkString("\n"))
      i
    }
    def enterScope(varName: String): LnTable = new LnTable(varName :: repr) // automatically shifts
  }
  object LnTable {
    val empty: LnTable = new LnTable(Nil)
  }

  def translateProg(t: dot.Tm): (ln.Tm, LabelTable) = {
    val labels: LabelTable = collectLabels(t)

    def translateVr(vars: LnTable, v: dot.Vr): ln.Vr = v match {
      case dot.Var(name) => ln.VarB(vars(name), name)
      case dot.VObj(selfName, ds) => ln.VObj(translateDms(vars.enterScope(selfName), ds), selfName)
    }

    def translateTm(vars: LnTable, t: dot.Tm): ln.Tm = t match {
      case dot.TmVar(v) => ln.TmVar(translateVr(vars, v))
      case dot.TmApp(receiver, label, arg) => ln.TmApp(translateTm(vars, receiver), labels(label), translateTm(vars, arg), label)
    }

    def translateDm(vars: LnTable, d: dot.Dm): ln.Dm = d match {
      case dot.DFun(name, argName, argTy, retTy, body) =>
        val vars2 = vars.enterScope(argName)
        ln.DFun(translateTy(vars, argTy), translateTy(vars2, retTy), translateTm(vars2, body), name, argName)
      case dot.DTy(name, tp) => ln.DTy(translateTy(vars, tp), name)
    }

    def translateDms(vars: LnTable, ds: Seq[dot.Dm]): Seq[ln.Dm] =  {
      labels.repr.map(label => ds.find(_.name == label) match {
        case Some(d) => translateDm(vars, d)
        case None => ln.DNone
      }).reverse.dropWhile(_ == ln.DNone)
    }

    def translateTy(vars: LnTable, t: dot.Ty): ln.Ty = t match {
      case dot.TBot => ln.TBot
      case dot.TTop => ln.TTop
      case dot.TFun(name, argName, argType, retType) =>
        val vars2 = vars.enterScope(argName)
        ln.TFun(labels(name), translateTy(vars, argType), translateTy(vars2, retType), name, argName)
      case dot.TMem(name, lo, hi) => ln.TMem(labels(name), translateTy(vars, lo), translateTy(vars, hi), name)
      case dot.TAlias(name, tp) => ln.TAlias(labels(name), translateTy(vars, tp), name)
      case dot.TSel(qual, sel) => ln.TSel(translateVr(vars, qual), labels(sel), sel)
      case dot.TBind(selfName, tp) => ln.TBind(translateTy(vars.enterScope(selfName), tp), selfName)
      case dot.TAnd(tp1, tp2) => ln.TAnd(translateTy(vars, tp1), translateTy(vars, tp2))
      case dot.TOr(tp1, tp2) => ln.TOr(translateTy(vars, tp1), translateTy(vars, tp2))
    }

    val u = translateTm(LnTable.empty, t)
    (u, labels)
  }

  def collectLabels(term: dot.Tm): LabelTable = {
    var labels = LabelTable.empty
    def encounter(label: String): Unit = {
      labels = labels.encounter(label)
    }
    
    def recVr(v: dot.Vr): Unit = v match {
      case dot.Var(name) => // NOP
      case dot.VObj(selfName, ds) => ds.foreach(recDm)
    }

    def recTm(t: dot.Tm): Unit = t match {
      case dot.TmVar(v) => recVr(v)
      case dot.TmApp(receiver, label, arg) => recTm(receiver); encounter(label); recTm(arg)
    }

    def recDm(d: dot.Dm): Unit = d match {
      case dot.DFun(name, argName, argTy, retTy, body) => encounter(name); recTy(argTy); recTy(retTy); recTm(body)
      case dot.DTy(name, tp) => encounter(name); recTy(tp)
    }

    def recTy(t: dot.Ty): Unit = t match {
      case dot.TBot => // NOP
      case dot.TTop => // NOP 
      case dot.TFun(name, argName, argType, retType) => encounter(name); recTy(argType); recTy(retType) 
      case dot.TMem(name, lo, hi) => encounter(name); recTy(lo); recTy(hi)
      case dot.TAlias(name, tp) => encounter(name); recTy(tp)
      case dot.TSel(qual, sel) => recVr(qual); encounter(sel)
      case dot.TBind(selfName, tp) => recTy(tp)
      case dot.TAnd(tp1, tp2) => recTy(tp1); recTy(tp2)
      case dot.TOr(tp1, tp2) => recTy(tp1); recTy(tp2)
    }

    recTm(term)

    labels
  }

}
