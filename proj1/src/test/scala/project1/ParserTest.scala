package project1

import java.io._
import org.scalatest._

class ParserTest extends FunSuite {

  def reader(src: String) = new BaseReader(src.iterator, '\u0000')
  def runner(src: String, gData: Map[Char,Int] = Map()) = new ASMRunner(src, gData)

  test("SingleDigit") {
    val gen = new SingleDigitParser(reader("4"))
    val ast = gen.parseCode

    assert(ast == Lit(4), "Invalid result")
  }

  // Function Helper for SingleAddOpParser
  def testSingleAdd(op: String, res: Exp) = {
    val gen = new SingleAddOpParser(reader(op))
    val ast = gen.parseCode

    assert(ast == res, "Invalid result")
  }

  test("SingleAddopAdd") {
    testSingleAdd("1+1", Plus(Lit(1),Lit(1)))
  }

  // Function Helper for MultipleAddOpParser
  def testMultipleAdd(op: String, res: Exp) = {
    val gen = new MultipleAddOpParser(reader(op))
    val ast = gen.parseCode

    assert(ast == res, "Invalid result")
  }

  test("MultipleAddopAdd") {
    testMultipleAdd("1+2", Plus(Lit(1), Lit(2)))
    testMultipleAdd("1+2+3", Plus(Plus(Lit(1), Lit(2)),Lit(3)))
  }

  test("MultipleAddopSub") {
    testMultipleAdd("1-2", Minus(Lit(1), Lit(2)))
    testMultipleAdd("1-2-3", Minus(Minus(Lit(1), Lit(2)), Lit(3)))
  }

  test("MultipleAddopAll") {
    testMultipleAdd("1", Lit(1))
    testMultipleAdd("1-2+3", Plus(Minus(Lit(1), Lit(2)), Lit(3)))
    testMultipleAdd("1+2-3", Minus(Plus(Lit(1), Lit(2)), Lit(3)))
  }

  // Function Helper for ArithOpParser
  def testArith(op: String, res: Exp) = {
    val gen = new ArithOpParser(reader(op))
    val ast = gen.parseCode

    assert(ast == res, "Invalid result")
  }

  test("ArithOpMul") {
    testArith("1*2", Times(Lit(1), Lit(2)))
    testArith("1*2*3", Times(Times(Lit(1), Lit(2)), Lit(3)))
  }

  test("ArithOpDiv") {
    testArith("4/3", Div(Lit(4), Lit(3)))
    testArith("4/3/3", Div(Div(Lit(4), Lit(3)), Lit(3)))
  }

  test("ArithOpAll") {
    testArith("1", Lit(1))
    testArith("5*3/7", Div(Times(Lit(5),Lit(3)),Lit(7)))
    testArith("4/3+2", Plus(Div(Lit(4), Lit(3)), Lit(2)))
    testArith("4*3-2", Minus(Times(Lit(4), Lit(3)), Lit(2)))
  }

  // Function Helper for ArithParOpParser
  def testArithPar(op: String, res: Exp) = {
    val gen = new ArithParOpParser(reader(op))
    val ast = gen.parseCode

    assert(ast == res, "Invalid result")
  }

  test("ArithOpPar") {
    testArithPar("(1)", Lit(1))
    testArithPar("((1))", Lit(1))
    testArithPar("(1+2)", Plus(Lit(1), Lit(2)))
    testArithPar("1+(2-3)", Plus(Lit(1), Minus(Lit(2), Lit(3))))
    testArithPar("1*(2-3)", Times(Lit(1), Plus(Lit(2))))
    testArithPar("1-((2*5)/6)", Minus(Lit(1), Div(Times(Lit(2), Lit(5)), Lit(6))))
  }
}
