package miniscala

import scala.collection.immutable.Seq

import miniscala.{MiniScalaTrees => mini}
import miniscala.{LocallyNamelessMiniScalaTrees => ln}

object MiniScalaTreesToLocallyNameless {

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
      if (i < 0) throw new NoSuchElementException(name + " not found")
      i
    }
    def enterScope(varName: String): LnTable = new LnTable(varName :: repr) // automatically shifts
  }
  object LnTable {
    val empty: LnTable = new LnTable(Nil)
  }

  def translateProg(t: mini.Trm): (ln.Trm, LabelTable) = {
    val labels: LabelTable = collectLabels(t)
    val vars: LnTable = LnTable.empty
    val u = translateTrm(labels, vars, t)
    (u, labels)
  }

  def collectLabels(term: mini.Trm): LabelTable = {
    var labels = LabelTable.empty
    def encounter(label: String): Unit = {
      labels = labels.encounter(label)
    }

    def recPth(p: mini.Pth): Unit = p match {
      case mini.PthVar(name) => // NOP
      case mini.PthSel(prefix, sel) => encounter(sel)
    }

    def recTrm(t: mini.Trm): Unit = t match {
      case mini.Var(name) => // NOP
      case mini.App(receiver, label, arg) => recTrm(receiver); encounter(label); recTrm(arg)
      case mini.New(cls) => recPth(cls)
      case mini.Block(stat, ret) => recDef(stat); recTrm(ret)
    }

    def recDef(d: mini.Def): Unit = d match {
      case mini.DefVal(name, typ, rhs) => encounter(name); recTyp(typ); recTrm(rhs)
      case mini.DefDef(name, argName, argTyp, retTyp, body) => encounter(name); recTyp(argTyp); recTyp(retTyp); recTrm(body)
      case mini.DefClass(name, selfName, defs) => encounter(name); defs.foreach(recDef)
    }

    def recTyp(t: mini.Typ): Unit = t match {
      case mini.TypCls(ref) => recPth(ref)
      case mini.TypMtd(argName, argTyp, retTyp) => recTyp(argTyp); recTyp(retTyp)
      case mini.TypOfCls(selfName, members) => members.foreach(recDef)
    }

    recTrm(term)

    labels
  }

  def translatePth(labels: LabelTable, vars: LnTable, p: mini.Pth): ln.Pth = p match {
    case mini.PthVar(name) => ln.PthVar(ln.VrBound(vars(name), name))
    case mini.PthSel(prefix, sel) => ln.PthSel(ln.VrBound(vars(prefix), prefix), labels(sel), sel)
  }

  def translateTrm(labels: LabelTable, vars: LnTable, t: mini.Trm): ln.Trm = t match {
    case mini.Var(name) => ln.Var(ln.VrBound(vars(name), name))
    case mini.App(receiver, label, arg) => ln.App(
      translateTrm(labels, vars, receiver),
      labels(label),
      translateTrm(labels, vars, arg),
      label
    )
    case mini.New(cls) => ln.New(translatePth(labels, vars, cls))
    case mini.Block(stat, ret) => ln.Block(
      translateDef(labels, vars, stat),
      translateTrm(labels, vars.enterScope(stat.name), ret)
    )
  }

  def translateDef(labels: LabelTable, vars: LnTable, d: mini.Def): ln.Def = d match {
    case mini.DefVal(name, typ, rhs) => ln.DefVal(translateTyp(labels, vars, typ), translateTrm(labels, vars, rhs), name)
    case mini.DefDef(name, argName, argTyp, retTyp, body) => ln.DefDef(
      translateTyp(labels, vars, argTyp),
      translateTyp(labels, vars.enterScope(argName), retTyp),
      translateTrm(labels, vars.enterScope(argName), body),
      name,
      argName
    )
    case mini.DefClass(name, selfName, defs) => ln.DefClass(translateDefs(labels, vars.enterScope(selfName), defs), name, selfName)
  }

  def translateDefs(labels: LabelTable, vars: LnTable, defs: Seq[mini.Def]): Seq[ln.Def] = {
    labels.repr.map(label => defs.find(_.name == label) match {
      case Some(d) => translateDef(labels, vars, d)
      case None => ln.DefNone
    })
  }

  def translateTyp(labels: LabelTable, vars: LnTable, t: mini.Typ): ln.Typ = t match {
    case mini.TypCls(ref) => ln.TypCls(translatePth(labels, vars, ref))
    case mini.TypMtd(argName, argTyp, retTyp) => ln.TypMtd(
      translateTyp(labels, vars, argTyp),
      translateTyp(labels, vars.enterScope(argName), retTyp),
      argName
    )
    case mini.TypOfCls(selfName, members) => ln.TypOfCls(translateDefs(labels, vars.enterScope(selfName), members), selfName)
  }

}
