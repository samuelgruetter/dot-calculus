object MutRecInh { def main(args: Array[String]): Unit = println({

  class Unit extends AnyRef
  val unit = new Unit

  class Lib1 extends AnyRef { lib1 =>
    class Entity extends AnyRef {
      // should of course return something more interesting
      def name(u: Unit): Unit = unit
    }

    class Author extends lib1.Entity {
      def book(u: Unit): lib1.Book = new lib1.Book
    }

    class Book extends lib1.Entity {
      def author(u: Unit): lib1.Author = new lib1.Author
    }

    def run(u: Unit): lib1.Book = {
      val a: lib1.Author = (new lib1.Book).author(unit)
      a.book(unit)
    }
  }
  val lib1: Lib1 = new Lib1
  lib1.run(unit)

})}
