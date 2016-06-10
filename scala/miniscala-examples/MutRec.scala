object MutRec { def main(args: Array[String]): Unit = println({

  class Unit
  val unit = new Unit
  
  class Lib1 { lib1 =>
    class Author {
      def book(u: Unit): lib1.Book = new lib1.Book
    }

    class Book {
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
