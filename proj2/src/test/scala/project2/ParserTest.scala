package project2

import java.io._
import org.scalatest._

class ParserTest extends FunSuite {
  import Language._

  def scanner(src: String) = new Scanner(new BaseReader(src, '\u0000'))

  def testGenericPrecedence(op: String, res: Exp) = {
    val gen = new ArithParser(scanner(op))
    val ast = gen.parseCode

    assert(ast == res, "Invalid result")
  }

  test("SingleDigit") {
    testGenericPrecedence("1", Lit(1))
  }

  test("GenericPrecedence") {
    testGenericPrecedence("2-4*3", Prim("-", Lit(2), Prim("*", Lit(4), Lit(3))))
  }
}
