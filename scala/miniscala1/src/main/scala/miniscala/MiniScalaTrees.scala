package miniscala

import scala.collection.immutable.Seq

/*
  p ::= x | x.l
  t ::= x | t.l | t t | new p | { ss; t }
  s ::= d
  d ::= val l: T = t | def m(x: S): T = t | class l { z => ds }
  T ::= p | (x:S)T | class { z => Ts }
  */
object MiniScalaTrees {

  sealed trait Pth {
    def subst(from: String, to: String): Pth
  }
  case class PthVar(name: String) extends Pth {
    def subst(from: String, to: String): PthVar = if (name == from) PthVar(to) else PthVar(name)
  }
  case class PthSel(prefix: String /*not (yet) Pth!*/, sel: String) extends Pth {
    def subst(from: String, to: String): PthSel = if (prefix == from) PthSel(to, sel) else PthSel(prefix, sel)
  }

  sealed trait Trm {
    def subst(from: String, to: String): Trm
  }
  case class Var(name: String) extends Trm {
    def subst(from: String, to: String): Var = if (name == from) Var(to) else Var(name)
  }
  case class App(receiver: Trm, label: String, arg: Trm) extends Trm {
    def subst(from: String, to: String) = App(receiver.subst(from, to), label, arg.subst(from, to))
  }
  case class New(cls: Pth) extends Trm {
    def subst(from: String, to: String) = New(cls.subst(from, to))
  }
  case class Block(stat: Stat, ret: Trm) extends Trm {
    def subst(from: String, to: String): Block = if (stat.name == from) {
      Block(stat, ret) // TODO what about var in type of DefVal?
    } else {
      Block(stat.subst(from, to), ret.subst(from, to))
    }
  }
  object Block {
    def apply(stats: Seq[Stat], ret: Trm): Trm = stats.foldRight(ret)((stat, oldRet) => Block(stat, oldRet))
  }

  type Stat = Def

  sealed trait Def {
    def name: String
    def subst(from: String, to: String): Def
  }
  case class DefVal(name: String, typ: Typ, rhs: Trm) extends Def {
    def subst(from: String, to: String): DefVal = {
      DefVal(name, typ.subst(from, to), rhs.subst(from, to))
    }
  }
  case class DefDef(name: String, argName: String, argTyp: Typ, retTyp: Typ, body: Trm) extends Def {
    def subst(from: String, to: String): DefDef = if (argName == from ) {
      DefDef(name, argName, argTyp.subst(from, to), retTyp, body)
    } else {
      DefDef(name, argName, argTyp.subst(from, to), retTyp.subst(from, to), body.subst(from, to))
    }
  }
  case class DefClass(name: String, selfName: String, defs: Seq[Def]) extends Def {
    def subst(from: String, to: String): DefClass = if (selfName == from) {
      DefClass(name, selfName, defs)
    } else {
      DefClass(name, selfName, defs.map(_.subst(from, to)))
    }
  }

  sealed trait Typ {
    def subst(from: String, to: String): Typ
  }
  case class TypCls(ref: Pth) extends Typ {
    def subst(from: String, to: String): Typ = TypCls(ref.subst(from, to))
  }
  case class TypMtd(argName: String, argTyp: Typ, retTyp: Typ) extends Typ {
    def subst(from: String, to: String): Typ = if (argName == from) {
      TypMtd(argName, argTyp.subst(from, to), retTyp)
    } else {
      TypMtd(argName, argTyp.subst(from, to), retTyp.subst(from, to))
    }
  }
  case class TypOfCls(selfName: String, members: Seq[Def]) extends Typ {
    def subst(from: String, to: String): TypOfCls = if (selfName == from) {
      TypOfCls(selfName, members)
    } else {
      TypOfCls(selfName, members.map(_.subst(from, to)))
    }
  }
}
