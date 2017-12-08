package project2

import org.scalatest._

class SemanticAnalyzerTest extends FunSuite {
  import Language._

  def testSemanticAnalyzer(ast: Exp, nWarning: Int, nError: Int) = {
    val fakeParser = new Parser(null) {
      override def error(msg: String, pos: Position) = {}
    }

    val analyzer = new SemanticAnalyzer(fakeParser)

    val (w, e) = analyzer.run(ast)
    assert(w == nWarning, "Icorrect number of Warnings")
    assert(e == nError, "Icorrect number of Warnings")
  }

  test("NoErrorNoWarning") {
    testSemanticAnalyzer(Lit(1), 0, 0)
    testSemanticAnalyzer(Prim("+", Lit(1), Lit(2)), 0, 0)
  }

}
