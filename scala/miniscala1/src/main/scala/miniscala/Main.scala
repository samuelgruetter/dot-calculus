package miniscala

import java.io.FileInputStream

object Main {
  val runUnused = false

  def main(args: Array[String]): Unit = {
    val path = args(0)
    val stream = new FileInputStream(path)

    println("--- Concrete Miniscala AST (in Scala) ---")
    val t1: MiniScalaTrees.Trm = Parser.parseMiniscala(stream)
    println(t1)
    println()

    if (runUnused) {
      println("--- Locally nameless Miniscala AST in Scala ---")
      val t2: LocallyNamelessMiniScalaTrees.Trm = MiniScalaTreesToLocallyNameless.translateProg(t1)._1
      println(t2)
      println()

      println("--- Locally nameless Miniscala AST in Coq ---")
      val s: String = LnMiniscalaToCoq.printTrm(t2)
      println(s)
      println()
    }

    println("--- Concrete DOT AST (in Scala) ---")
    val t3: DotTrees.Tm = MiniScalaToDot.translateProg(t1)
    println(t3)
    println()

    println("--- Locally nameless DOT AST (in Scala) ---")
    val t4: LocallyNamelessDotTrees.Tm = DotTreesToLocallyNameless.translateProg(t3)._1
    println(t4)
    println()

    println("--- Locally nameless DOT AST (in Coq) ---")
    val s2: String = LnDotToCoq.printTm(t4)
    println(s2)
    println()
  }
}
