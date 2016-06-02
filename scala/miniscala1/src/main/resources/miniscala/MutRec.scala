object MutRec { def main(args: Array[String]): Unit = println({

  class Unit
  val unit = new Unit
  
  class Lib1 { z =>
    class Author {
      def book(u: Unit): z.Book = new z.Book
    }

    class Book {
      def author(u: Unit): z.Author = new z.Author
    }

    def run(u: Unit): z.Book = {
      val a: z.Author = (new z.Book).author(unit)
      a.book(unit)
    }
  }
  val lib1: Lib1 = new Lib1
  lib1.run(unit)

})}
