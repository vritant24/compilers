package miniscala

import java.io._
import scala.io._

import CPSTreeFormatter._

object Main extends MainHelper {
  def main(args: Array[String]): Unit = {

    val (src, idxToPos) = if (new File(args(0)).exists) {
      MiniScalaFileReader.readFiles(args)
    } else {
      (args(0), (x: Int) => ("console", x))
    }

    println(src)

    val reader = new BaseReader(src, '\u0000')
    val scanner = new Scanner(reader, idxToPos)

    // Parser to test!
    val parser = new MiniScalaParser(scanner)
    val ast = try {
      parser.parseCode
    } catch {
      case e: AbortException => return
      case e: Throwable => throw e
    }

    println("=========================")
    println(ast)
    println("=========================\n")

    val analyzer = new SemanticAnalyzer(parser)
    val (nast, numWarning, numError) = analyzer.run(ast)
    if (numError > 0) {
      return
    }

    println("=========================")
    println(nast)
    println("=========================\n")

    val backEnd = (
      CMScalaToCPSTranslator
      andThen treePrinter("Tree in CPS")
      andThen passThrough(SymbolicCPSTreeChecker)
      andThen CPSInterpreterHigh
    )
    try {
      backEnd(nast)
    } catch {
      case MiniScalaFatalError(msg) =>
        println(msg)
        sys.exit(1)
    }

  }
}

trait MainHelper {
  protected def treePrinter[T](msg: String)(implicit f: Formatter[T]): T => T =
    passThrough { tree =>
      val writer = new java.io.PrintWriter(System.out)
      writer.println(msg)
      f.toDocument(tree).format(80, writer)
      writer.println()
      writer.flush()
    }

  protected def passThrough[T](f: T => Unit): T=>T = { t: T => f(t); t }

  protected def seqPrinter[T](msg: String): Seq[T] => Seq[T] =
    passThrough { program =>
      println(msg)
      for (elem <- program)
        println(elem)
    }
}
