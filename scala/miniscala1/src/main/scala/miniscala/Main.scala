package miniscala

object Main {
  def main(args: Array[String]): Unit = {
    val stream = getClass.getResourceAsStream("MutRec.scala")
    val t1: MiniScalaTrees.Trm = Parser.parseMiniscala(stream)
    println(t1)
    println()
    val t2: LocallyNamelessMiniScalaTrees.Trm = MiniScalaTreesToLocallyNameless.translateProg(t1)._1
    println(t2)
    println()
    val s: String = LnMiniscalaToCoq.printTrm(t2)
    println(s)
    println()
  }
}
