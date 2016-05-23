object MutRec { z =>
  class U // Unit

  class Author {
    def book(u: z.U): z.Book = new z.Book
  }

  class Book {
    def author(u: z.U): z.Author = new z.Author
  }

  def run(u: z.U): z.Book = {
    val a = (new z.Book).author(new z.U)
    a.book(new z.U)
  }

  def main(args: Array[String]): Unit = {
    println(new z.Book)
  }
}
