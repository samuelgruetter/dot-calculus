package miniscala

import scala.collection.immutable.Seq
import scala.meta._

import miniscala.{MiniScalaTrees => m}

object Parser {
  def main(args: Array[String]): Unit = {
    val stream = getClass.getResourceAsStream("MutRec.scala")
    val tree = stream.parse[Source]
    println(parseTopLevel(tree))
  }

  // https://github.com/scalameta/scalameta/blob/master/docs/quasiquotes.md

  implicit def termNameToString(n: Term.Name): String = n.toString()
  implicit def typeNameToString(n: Type.Name): String = n.toString()
  implicit def termParamNameToString(n: Term.Param.Name): String = n.toString()
  implicit def ctorNameToString(n: Ctor.Name): String = n.toString()

  def parseTopLevel(tree: Source): m.Trm = {
    tree match {
      case source"""
        object $mainObjName { def main(args: Array[String]): Unit = println($aexpr) }"""
      => aexpr match {
        case arg"${expr: Term}" => parseTrm(expr)
      }
    }
  }

  def parseSelfRef(selfParam: Term.Param): String = selfParam match {
    case param"$selfName: $selfType" => selfType match {
      case Some(_) => sys.error("explicit self type is not supported")
      case None => selfName
    }
  }

  def parseStats(stats: Seq[Stat]): Seq[m.Stat] = {
    stats.map(parseStat)
  }

  def log[X](p: X)(implicit style: Structure[X]): Unit = {
    println(s"$p --- ${p.show[Structure]} --- ${p.getClass}")
  }

  def parseStat(stat: Stat): m.Stat = stat match {
    case q"val $pat: $tpeopt = $expr" => tpeopt match {
      case Some(tp: Type) => pat match {
        case q"${name: Pat.Var.Term}" => m.DefVal(name.toString(), parseTyp(tp), parseTrm(expr))
      }
      case None => sys.error("val must have explicit type")
    }
    case q"def $name(${argName: Term.Name}: $argTp0): $tpeopt = $expr" => tpeopt match {
      case Some(retTp: Type) => argTp0 match {
        case Some(targ"${argTp: Type}") => m.DefDef(name, argName, parseTyp(argTp), parseTyp(retTp), parseTrm(expr))
      }
      case None => sys.error("def must have explicit return type")
    }
    case q"class $cname { $selfParam => ..$stats }" =>
      m.DefClass(cname, parseSelfRef(selfParam), parseStats(stats))
  }

  def parseTrm(t: Term): m.Trm = t match {
    case q"${name: Term.Name}" => m.Var(name)
    case q"$expr1.$l($aexpr)" =>
      aexpr match {
        case arg"${expr2: Term}" => m.App(parseTrm(expr1), l, parseTrm(expr2))
      }
    case q"new { ..$stat } with ..$ctorcalls { $param => ..$stats }" => ctorcalls match {
      case ctorcall :: Nil => ctorcall match {
        case ctor"${ctorname: Ctor.Name}" => m.New(m.PthVar(ctorname))
        case ctor"${x: Term.Name}.$ctorname" => m.New(m.PthSel(x, ctorname))
      }
    }
    case q"{ ..$stats; ${retExpr: Term} }" => m.Block(parseStats(stats), parseTrm(retExpr))
  }

  def parseTyp(t: Type): m.Typ = t match {
    case t"${name: Type.Name}" => m.TypCls(m.PthVar(name))
    case t"$ref.$tname" => ref match {
      case t"${prefix: Term.Name}" => m.TypCls(m.PthSel(prefix, tname))
    }
  }
}
