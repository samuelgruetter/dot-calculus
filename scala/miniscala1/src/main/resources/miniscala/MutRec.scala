object MutRec {

  def main(args: Array[String]): Unit = println({

    // begin of actual program

    class Lib1 { z =>
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
    }
    val lib1 = new Lib1
    lib1.run(new lib1.U)

    // end of actual program
  })
}

/*
Translation into DOT:

// definition of class inside expr is replaced by only a wrapper object containing the signature, but no implementation
// Note that Lib1.L0 is never used in this example, but it's generated anyways
let Lib1 = new {
  L0: { z =>
    { type U = { y => Top } } /\
    { type Author = { y => def book(u: z.U): z.Book } } /\
    { type Book = { y => def author(u: z.U): z.Author } } /\
    { def run(u: z.U): z.Book }
  }
} in
// the implementation is repeated every time a new instance is created
let lib1 = new { z =>
  type U = { y => Top }
  type Author = { y => def book(u: z.U): z.Book }
  type Book = { y => def author(u: z.U): z.Author }
  def run(u: z.U): z.Book = {
    let a = (new {
      def author(u: z.U): z.Author = new {
        def book(u: z.U): z.Book = OH NO, expanding the constructors at each usage results in infinite loops!!!!
      }
    }).author(new {}) in a.book(new {})
  }
} in
lib1.run(new {})

 */