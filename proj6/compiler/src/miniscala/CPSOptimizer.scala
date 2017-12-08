package miniscala

import scala.collection.mutable.{ Map => MutableMap }

abstract class CPSOptimizer[T <: CPSTreeModule { type Name = Symbol }]
  (val treeModule: T) {
  import treeModule._

  def apply(tree: Tree): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = (size(simplifiedTree) * 1.5).toInt
    fixedPoint(simplifiedTree, 8) { t => inline(t, maxSize) }
  }

  /* Counts how many times a symbol is encountered as an applied function,
   * and how many as a value
   */
  private case class Count(applied: Int = 0, asValue: Int = 0)

  /* Local state of the optimization
   * Note: To update the state, use the with* methods
   */
  private case class State(
    /* How many times a symbol is encountered in the Tree. Note: The
     * census for the whole program gets calculated once in the
     * beginning, and passed to the initial state.
     */
    census: Map[Name, Count],
    // Name substitution that needs to be applied to the current tree
    subst: Substitution[Name] = Substitution.empty,
    // Names that have a constant value
    lEnv: Map[Name, Literal] = Map.empty,
    // The inverse of lEnv
    lInvEnv: Map[Literal, Name] = Map.empty,
    // A known block mapped to its tag and length
    bEnv: Map[Name, (Literal, Name)] = Map.empty,
    // ((p, args) -> n2) is included in eInvEnv iff n2 == p(args)
    // Note: useful for common-subexpression elimination
    eInvEnv: Map[(ValuePrimitive, Seq[Name]), Name] = Map.empty,
    // Continuations that will be inlined
    cEnv: Map[Name, CntDef] = Map.empty,
    // Functions that will be inlined
    fEnv: Map[Name, FunDef] = Map.empty,
    // Functions with their arg values
    fArgs: Map[Name, Seq[Literal]] = Map.empty) {

    // Checks whether a symbol is dead in the current state
    def dead(s: Name): Boolean =
      census get s map (_ == Count(applied = 0, asValue = 0)) getOrElse true
    // Checks whether a symbol is applied exactly once as a function
    // in the current State, and never used as a value
    def appliedOnce(s: Name): Boolean =
      census get s map (_ == Count(applied = 1, asValue = 0)) getOrElse false

    // Adds a substitution to the state
    def withSubst(from: Name, to: Name): State =
      copy(subst = subst + (from -> to))
    // Adds a Seq of substitutions to the state
    def withSubst(from: Seq[Name], to: Seq[Name]): State =
      copy(subst = subst ++ (from zip to))

    // Adds a constant to the State
    def withLit(name: Name, value: Literal) =
      copy(lEnv = lEnv + (name -> value), lInvEnv = lInvEnv + (value -> name))
    // Adds a block to the state
    def withBlock(name: Name, tag: Literal, size: Name) =
      copy(bEnv = bEnv + (name -> (tag, size)))
    // Adds a primitive assignment to the state
    def withExp(name: Name, prim: ValuePrimitive, args: Seq[Name]) =
      copy(eInvEnv = eInvEnv + ((prim, args) -> name))
    // Adds an inlinable continuation to the state
    def withCnt(cnt: CntDef) =
      copy(cEnv = cEnv + (cnt.name -> cnt))
    // Adds a Seq of inlinable continuations to the state
    def withCnts(cnts: Seq[CntDef]) =
      (this /: cnts) (_.withCnt(_))
    // Adds an inlinable function to the state
    def withFun(fun: FunDef) =
      copy(fEnv = fEnv + (fun.name -> fun))
    // Adds a Seq of inlinable functions to the state
    def withFuns(funs: Seq[FunDef]) =
      (this /: funs) (_.withFun(_))
    // Adds a Function with its arguement values
    def withFunArgs(fun: Name, args: Seq[Literal]) =
      copy(fArgs = fArgs + (fun -> args))
    /*
     * The same state, with emply inverse environments.
     * Use this when entering a new FunDef, because assigned Name's may
     * come out of scope during hoisting.
     */
    def withEmptyInvEnvs =
      copy(lInvEnv = Map.empty, eInvEnv = Map.empty)
  }

  // Shrinking optimizations

  private def shrink(tree: Tree): Tree = {
    def shrinkT(tree: Tree)(implicit s: State): Tree = tree match {
      
      /*============================ LETL ============================*/
      
      //if variable is dead
      case LetL(x, v, body) if (s.dead(x)) =>
        shrinkT(body)

      //if a variable defined before has the same value
      case LetL(x, v, body) if (s.lInvEnv.contains(v)) => 
        shrinkT(body)(s.withSubst(x, s.lInvEnv(v)))
      

      //base case LetL
      case LetL(x, v, body) => 
        LetL(x, v, shrinkT(body)(s.withLit(x,v)))
      
      /*==============================================================*/
      /*============================ LETP ============================*/
      
      //if variable is dead
      case LetP(x, op, args, body) if(s.dead(x)) && !unstable(op) && !impure(op) =>
        shrinkT(body)

      //if a variable defined before has the same value
      case LetP(x, op, args, body) if(s.eInvEnv.contains((op, args))) && !unstable(op) && !impure(op) => 
        shrinkT(body)(s.withSubst(x, s.eInvEnv(op, args)))

      //same args reduce
      case LetP(x, op, args, body) if(args.forall(_ == args.head) && sameArgReduce.isDefinedAt(op)) => 
        if(sameArgReduce.isDefinedAt(op)) {
          val v = sameArgReduce.apply(op)
          LetL(x, v, shrinkT(body)(s.withLit(x, v)))
        }
        else {
          //replace any values needing substitution
          val nargs = args map { n => s.subst(n) }
          LetP(x, op, nargs, shrinkT(body)(s.withExp(x, op, args)))
        }

      //left neutral
      case LetP(x, op, args, body) if(args.length == 2 && s.lEnv.contains(args(0)) && leftNeutral.contains((s.lEnv(args(0)), op))) =>
        val y = args(1)
        shrinkT(body)(s.withSubst(x, y))

      //right neutral
      case LetP(x, op, args, body) if(args.length == 2 && s.lEnv.contains(args(1)) && rightNeutral.contains((op, s.lEnv(args(1))))) =>
        val y = args(0)
        shrinkT(body)(s.withSubst(x, y))

      //left absorbing
      case LetP(x, op, args, body) if(args.length == 2 && s.lEnv.contains(args(0)) && leftAbsorbing.contains((s.lEnv(args(0)), op))) =>
        val v = s.lEnv(args(0))
        LetL(x, v, shrinkT(body)(s.withLit(x,v)))

      //right absorbing
      case LetP(x, op, args, body) if(args.length == 2 && s.lEnv.contains(args(1)) && rightAbsorbing.contains((op, s.lEnv(args(1))))) =>
        val v = s.lEnv(args(1))
        LetL(x, v, shrinkT(body)(s.withLit(x,v))) 
      
      //blockalloc 202
      case LetP(x, op, args, body) if(blockAllocTag.isDefinedAt(op) && (blockAllocTag(op) == IntLit(202) || blockAllocTag(op) == IntLit(1))) =>
        //replace any values needing substitution
        val nargs = args map { n => s.subst(n) }
        LetP(x, op, nargs, shrinkT(body)(s.withBlock(x, blockAllocTag.apply(op), args(0))))

      //blockset
      case LetP(x, op, args, body) if(blockSet == op) => 
        //replace any values needing substitution
        val nargs = args map { n => s.subst(n) }
        LetP(x, op, nargs, shrinkT(body)(s.withExp(args(2), op, Seq(args(0), args(1)))))
      
      //blockget
      case LetP(x, op, args, body) if(blockGet == op) => 
        //replace any values needing substitution
        val nargs = args map { n => s.subst(n) }
        if(s.eInvEnv.contains((blockSet, args))) {
          val v = s.eInvEnv((blockSet, args))
          shrinkT(body)(s.withSubst(x, v))
        } 
        else {
          LetP(x, op, nargs, shrinkT(body)(s.withExp(x, op, args)))
        }

      //blocktag
      case LetP(x, op, args, body) if(op == blockTag) =>
        val nargs = args map { n => s.subst(n) }
        if(s.bEnv.contains(nargs(0))) {
          shrinkT(body)(s.withSubst(x, nargs(0)))
        } else {
          LetP(x, op, nargs, shrinkT(body))
        }

      //ID
      case LetP(x, op, args, body) if(op == identity) =>
        shrinkT(body)(s.withSubst(x, args(0)))

      //Constant Propogation
      case LetP(x, op, args, body) if(args.forall(n => s.lEnv.contains(n))) =>
        //replace any values needing substitution
        val nargs = args map { n => s.subst(n) }

        val vargs = args map { n => s.lEnv(n) }
        if(vEvaluator.isDefinedAt((op, vargs))) {
          val value = vEvaluator.apply((op, vargs))
          LetL(x, value, shrinkT(body)(s.withLit(x, value)))
        } 
        else {
          LetP(x, op, nargs, shrinkT(body)(s.withExp(x, op, args)))
        }

      //base case LetP
      case LetP(x, op, args, body) =>
        //replace any values needing substitution
        val nargs = args map { n => s.subst(n) }
        LetP(x, op, nargs, shrinkT(body)(s.withExp(x, op, args)))

      /*==============================================================*/
      /*============================ LETF ============================*/
  
      case LetF(funs, body) => 
        var finl = List[FunDef]()
        var nfuns = List[FunDef]()

        funs.foreach {
          case f@FunDef(n, retC, args, fbody) =>
            //filter for dead functions
            if(!s.dead(n)){
              nfuns = f :: nfuns
              if(s.appliedOnce(n)) {
                finl = f :: finl
              } 
            }    
        }
        
        //apply shrinkT on function body
        val nnfuns = nfuns.reverse map {
          case FunDef(n, retC, args, fbody) => FunDef(n, retC, args, shrinkT(fbody)(s.withEmptyInvEnvs.withFuns(finl)))
        }
        
        if(nnfuns.length == 0) {
          shrinkT(body)
        } else {
          LetF(nnfuns, shrinkT(body)(s.withFuns(finl)))
        }

      /*==============================================================*/
      /*============================ LETC ============================*/

      case LetC(cnts, body) =>
        var ncnts = List[CntDef]()
        cnts.foreach {
          case c@CntDef(n, args, cbody) =>
            if(!s.dead(n)){
              ncnts = c :: ncnts
            }
        }

        val nncnts = ncnts.reverse map {
          case CntDef(n, args, body) => CntDef(n, args, shrinkT(body)(s.withEmptyInvEnvs))
        }
        
        if(nncnts.length == 0) {
          shrinkT(body)
        } else {
          LetC(nncnts, shrinkT(body))
        }
        // LetC(cnts, shrinkT(body))
      /*==============================================================*/
      /*============================ APPC ============================*/

      case AppC(cnt, args) =>
        //replace any values needing substitution
        val c = s.subst(cnt)
        val nargs = args map { n => s.subst(n) }

        AppC(c, nargs)
         
      //*==============================================================*/
      /*============================ APPF ============================*/

      case AppF(fun, retC, args) if(s.fEnv.contains(fun)) =>
        val nretC = s.subst(retC)
        val nfun = s.fEnv(fun)
        shrinkT(nfun.body)(s.withSubst(nfun.args :+ nfun.retC, args :+ nretC))

      case AppF(fun, retC, args) =>
        //replace any values needing substitution
        val nretC = s.subst(retC)
        val f = s.subst(fun)
        val nargs = args map { n => s.subst(n) }

        AppF(f, nretC, nargs)

      /*==============================================================*/
      /*============================  IF  ============================*/

      //same args reduce
      case If(cond, args, thenC, elseC) if(args.forall(_ == args.head) && args.length > 1) => 
        val v = sameArgReduceC.apply(cond)
        if(v) {
          AppC(thenC, Seq())
        } else {
          AppC(elseC, Seq())
        }

      //constant propogation
      case If(cond, args, thenC, elseC) if(args.forall(n => s.lEnv.contains(n))) => 
        //replace any values needing substitution
        val nargs = args map { n => s.subst(n) }

        //get values for args
        val vargs = nargs map { n => s.lEnv(n) }
        if(cEvaluator.isDefinedAt((cond, vargs))) {
          val value = cEvaluator.apply((cond, vargs))

          if(value) {
            AppC(thenC, Seq())
          } else {
            AppC(elseC, Seq())
          }
        } else {
          If(cond, nargs, thenC, elseC)
        }

      case If(cond, args, thenC, elseC) =>
        //replace any values needing substitution
        val nargs = args map { n => s.subst(n) }
        If(cond, nargs, thenC, elseC)

      /*==============================================================*/
      /*============================ HALT ============================*/
      
      case Halt(arg) =>
        //substitute arg if need be
        Halt(s.subst(arg))
      
      /*==============================================================*/
      /*============================ BASE ============================*/
      case _ =>
        // TODO
        tree
      /*==============================================================*/
    }

    shrinkT(tree)(State(census(tree)))
    
  }

  // (Non-shrinking) inlining

  def inlineSubstT(tree: Tree)(implicit s: State): Tree = tree match {
      /*==============================================================*/
      case LetL(x, v, body) => 
        val nx = Symbol.fresh("$xl")
        LetL(nx, v, inlineSubstT(body)(s.withSubst(x, nx)))
      /*==============================================================*/
      case LetP(x, op, args, body) =>
        val nx = Symbol.fresh("$xp")
        val nargs = args map { n => s.subst(n) }
        LetP(nx, op, nargs, inlineSubstT(body)(s.withSubst(x, nx)))
      /*==============================================================*/
      case If(cond, args, thenC, elseC) =>
        val nargs = args map { n => s.subst(n) }
        val nthenC = s.subst(thenC)
        val nelseC = s.subst(elseC)
        If(cond, nargs, nthenC, nelseC)
      /*==============================================================*/
      case Halt(arg) =>
          Halt(s.subst(arg))
      /*==============================================================*/
      case LetC(cnts, body) =>
        var nnames = List[Name]()
        var onames = List[Name]()
        val ncnts = cnts map {
          case CntDef(n, args, cbody) =>
            val nx = Symbol.fresh("$r")
            onames = n :: onames
            nnames = nx :: nnames
            CntDef(nx, args, cbody)
        }

        val nncnts = ncnts map {
          case CntDef(n, args, cbody) =>
            CntDef(n, args, inlineSubstT(cbody)(s.withSubst(onames, nnames)))
        }

        LetC(nncnts, inlineSubstT(body)(s.withSubst(onames, nnames)))
      /*==============================================================*/
      case LetF(funs, body) =>
        var nnames = List[Name]()
        var onames = List[Name]()

        val nfuns = funs map {
          case FunDef(n, retC, args, fbody) =>
            val nx = Symbol.fresh("$f")
            onames = n :: onames
            nnames = nx :: nnames
            FunDef(nx, retC, args, inlineSubstT(fbody)(s.withSubst(n, nx)))
        }

        val nnfuns = nfuns map {
          case FunDef(n, retC, args, fbody) =>
            FunDef(n, retC, args, inlineSubstT(fbody)(s.withSubst(onames, nnames)))
        }

        LetF(nnfuns, inlineSubstT(body)(s.withSubst(onames, nnames)))
      /*==============================================================*/
      case AppF(fun, retC, args) =>
        val nretC = s.subst(retC)
        val nargs = args map { n => s.subst(n) }
        val nfun = s.subst(fun)
        AppF(nfun, nretC, nargs)
      /*==============================================================*/
      case AppC(cnt, args) =>
        val nargs = args map { n => s.subst(n) }
        val ncnt = s.subst(cnt)
        AppC(ncnt, nargs)
      /*==============================================================*/
    }

  private def inline(tree: Tree, maxSize: Int): Tree = {

    val fibonacci = Seq(1, 2, 3, 5, 8, 13, 21)

    val trees = Stream.iterate((0, tree), fibonacci.length) { case (i, tree) =>
      val funLimit = fibonacci(i)
      val cntLimit = i

      def inlineT(tree: Tree)(implicit s: State): Tree = tree match {
        /*==============================================================*/
        case LetL(x, v, body) => 
          LetL(x, v, inlineT(body))
        /*==============================================================*/
        case LetP(x, op, args, body) =>
          LetP(x, op, args, inlineT(body))
        /*==============================================================*/
        case If(cond, args, thenC, elseC) =>
          If(cond, args, thenC, elseC)
        /*==============================================================*/
        case Halt(arg) =>
          Halt(arg)
        /*==============================================================*/
        case LetC(cnts, body) =>
          var cinl = List[CntDef]()
          // make new names
          val ncnts = cnts map {
            case c@CntDef(n, args, cbody) =>
              val si = size(cbody)
              if(si < cntLimit) {
                cinl = c :: cinl
              }
              c
          }
          //apply inline and substitution in each fbody
          val nncnts = ncnts map {
            case c@CntDef(n, args, cbody) => 
              CntDef(n, args, inlineT(cbody)(s.withEmptyInvEnvs.withCnts(cinl.filter(_ != c))))
          }
          LetC(nncnts, inlineT(body)(s.withCnts(cinl)))

        /*==============================================================*/

        case LetF(funs, body) =>
          var finl = List[FunDef]()

          val nfuns = funs map {
            case f@FunDef(n, retC, args, fbody) =>
              //check inlinable
              val si = size(fbody)
              if(si < funLimit) {
                finl = f :: finl
              }
              f
          }
          //apply inline and substitution in each fbody
          val nnfuns = nfuns map {
            case f@FunDef(n, retC, args, fbody) =>
              FunDef(n, retC, args, inlineT(fbody)(s.withEmptyInvEnvs.withFuns(finl.filter(_ != f))))
          }
          LetF(nnfuns, inlineT(body)(s.withFuns(finl)))
        
        /*==============================================================*/

        case AppC(cnt, args) =>
          val nargs = args map { n => s.subst(n) }
          val ncnt = s.subst(cnt)
          if(s.cEnv.contains(ncnt)) {
            var ncntdef = s.cEnv(ncnt)
            inlineSubstT(ncntdef.body)(s.withSubst(ncntdef.args, nargs))
          } else {
            AppC(ncnt, nargs)
          }

        /*==============================================================*/ 

        case AppF(fun, retC, args) =>
          val nretC = s.subst(retC)
          val nargs = args map { n => s.subst(n) }
          val nfun = s.subst(fun)
          if(s.fEnv.contains(nfun)) {
            val nfundef = s.fEnv(nfun)
            inlineSubstT(nfundef.body)(s.withSubst(nfundef.args :+ nfundef.retC, nargs :+ nretC))          
          } else {
            AppF(nfun, nretC, nargs)
          }

        /*==============================================================*/
      }

      (i + 1, fixedPoint(inlineT(tree)(State(census(tree))))(shrink))
    }

    

    trees.takeWhile{ case (_, tree) => size(tree) <= maxSize }.last._2
  }

  // Census computation
  private def census(tree: Tree): Map[Name, Count] = {
    val census = MutableMap[Name, Count]()
    val rhs = MutableMap[Name, Tree]()

    def incAppUse(symbol: Name): Unit = {
      val currCount = census.getOrElse(symbol, Count())
      census(symbol) = currCount.copy(applied = currCount.applied + 1)
      rhs remove symbol foreach addToCensus
    }

    def incValUse(symbol: Name): Unit = {
      val currCount = census.getOrElse(symbol, Count())
      census(symbol) = currCount.copy(asValue = currCount.asValue + 1)
      rhs remove symbol foreach addToCensus
    }

    def addToCensus(tree: Tree): Unit = (tree: @unchecked) match {
      case LetL(_, _, body) =>
        addToCensus(body)
      case LetP(_, _, args, body) =>
        args foreach incValUse; addToCensus(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); addToCensus(body)
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); addToCensus(body)
      case AppC(cnt, args) =>
        incAppUse(cnt); args foreach incValUse
      case AppF(fun, retC, args) =>
        incAppUse(fun); incValUse(retC); args foreach incValUse
      case If(_, args, thenC, elseC) =>
        args foreach incValUse; incValUse(thenC); incValUse(elseC)
      case Halt(arg) =>
        incValUse(arg)
    }

    addToCensus(tree)
    census.toMap
  }

  private def sameLen(formalArgs: Seq[Name], actualArgs: Seq[Name]): Boolean =
    formalArgs.length == actualArgs.length

  // private def bound(tree: Tree, list: List[Name]): List[Name] = (tree: @unchecked) match {
  //   case LetL(x, _, body) => x :: list
  //   case LetP(_, _, _, body) => bound(body, list)
  //   case LetC(cs, body) => (cs map { c => size(c.body) }).sum :: bound(body, list)
  //   case LetF(fs, body) => (fs map { f => size(f.body) }).sum :: bound(body, list)
  //   case AppC(_, _) | AppF(_, _, _) | If(_, _, _, _) | Halt(_) => list
  // }

  private def size(tree: Tree): Int = (tree: @unchecked) match {
    case LetL(_, _, body) => size(body) + 1
    case LetP(_, _, _, body) => size(body) + 1
    case LetC(cs, body) => (cs map { c => size(c.body) }).sum + size(body)
    case LetF(fs, body) => (fs map { f => size(f.body) }).sum + size(body)
    case AppC(_, _) | AppF(_, _, _) | If(_, _, _, _) | Halt(_) => 1
  }

  // Returns whether a ValuePrimitive has side-effects
  protected val impure: ValuePrimitive => Boolean
  // Returns whether different applications of a ValuePrimivite on the
  // same arguments may yield different results
  protected val unstable: ValuePrimitive => Boolean
  // Extracts the tag from a block allocation primitive
  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal]
  // Returns true for the block tag primitive
  protected val blockTag: ValuePrimitive
  // Returns true for the block Get primitive
  protected val blockGet: ValuePrimitive
  // Returns true for the block Set primitive
  protected val blockSet: ValuePrimitive
  // Returns true for the block length primitive
  protected val blockLength: ValuePrimitive
  // Returns true for the identity primitive
  protected val identity: ValuePrimitive

  // ValuePrimitives with their left-neutral elements
  protected val leftNeutral: Set[(Literal, ValuePrimitive)]
  // ValuePrimitives with their right-neutral elements
  protected val rightNeutral: Set[(ValuePrimitive, Literal)]
  // ValuePrimitives with their left-absorbing elements
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)]
  // ValuePrimitives with their right-absorbing elements
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)]
  // ValuePrimitives with the value equal arguments reduce to
  protected val sameArgReduce: PartialFunction[ValuePrimitive, Literal]
  // TestPrimitives with the (boolean) value equal arguments reduce to
  protected val sameArgReduceC: TestPrimitive => Boolean
  // An evaluator for ValuePrimitives
  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal]
  // An evaluator for TestPrimitives
  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean]
}

object CPSOptimizerHigh extends CPSOptimizer(SymbolicCPSTreeModule)
    with (SymbolicCPSTreeModule.Tree => SymbolicCPSTreeModule.Tree) {
  import treeModule._

  protected val impure: ValuePrimitive => Boolean =
    Set(MiniScalaBlockSet, MiniScalaByteRead, MiniScalaByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case MiniScalaBlockAlloc(_) | MiniScalaBlockGet | MiniScalaByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case MiniScalaBlockAlloc(tag) => IntLit(tag)
  }
  protected val blockTag: ValuePrimitive = MiniScalaBlockTag
  protected val blockGet: ValuePrimitive = MiniScalaBlockGet
  protected val blockSet: ValuePrimitive = MiniScalaBlockSet
  protected val blockLength: ValuePrimitive = MiniScalaBlockLength

  protected val identity: ValuePrimitive = MiniScalaId

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((IntLit(0), MiniScalaIntAdd), (IntLit(1), MiniScalaIntMul), (IntLit(~0), MiniScalaIntBitwiseAnd), (IntLit(0), MiniScalaIntBitwiseOr), (IntLit(0), MiniScalaIntBitwiseXOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((MiniScalaIntAdd, IntLit(0)), (MiniScalaIntSub, IntLit(0)), (MiniScalaIntMul, IntLit(1)), (MiniScalaIntDiv, IntLit(1)),
        (MiniScalaIntArithShiftLeft, IntLit(0)), (MiniScalaIntArithShiftRight, IntLit(0)),
        (MiniScalaIntBitwiseAnd, IntLit(~0)), (MiniScalaIntBitwiseOr, IntLit(0)), (MiniScalaIntBitwiseXOr, IntLit(0)))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((IntLit(0), MiniScalaIntMul), (IntLit(0), MiniScalaIntBitwiseAnd), (IntLit(~0), MiniScalaIntBitwiseOr))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((MiniScalaIntMul, IntLit(0)), (MiniScalaIntBitwiseAnd, IntLit(0)), (MiniScalaIntBitwiseOr, IntLit(~0)))

  protected val sameArgReduce: PartialFunction[ValuePrimitive, Literal] =
    Map(MiniScalaIntSub -> IntLit(0), MiniScalaIntDiv -> IntLit(1), MiniScalaIntMod -> IntLit(0), MiniScalaIntBitwiseXOr -> IntLit(0))

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case MiniScalaIntLe | MiniScalaIntGe | MiniScalaEq => true
    case MiniScalaIntLt | MiniScalaIntGt | MiniScalaNe => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (MiniScalaIntToChar, Seq(IntLit(v)))          => CharLit(v.toChar)
    case (MiniScalaCharToInt, Seq(CharLit(v)))         => IntLit(v.toInt)

    case (MiniScalaIntAdd, Seq(IntLit(x), IntLit(y))) => IntLit(x + y)
    case (MiniScalaIntSub, Seq(IntLit(x), IntLit(y))) => IntLit(x - y)
    case (MiniScalaIntMul, Seq(IntLit(x), IntLit(y))) => IntLit(x * y)
    case (MiniScalaIntDiv, Seq(IntLit(x), IntLit(y))) => if (y!= 0) IntLit(Math.floorDiv(x, y)) else IntLit(0)
    case (MiniScalaIntMod, Seq(IntLit(x), IntLit(y))) => if (y!= 0) IntLit(Math.floorMod(x, y)) else IntLit(0)

    case (MiniScalaIntArithShiftLeft,   Seq(IntLit(x), IntLit(y)))  => IntLit(x << y)
    case (MiniScalaIntArithShiftRight,  Seq(IntLit(x), IntLit(y)))  => IntLit(x >> y)
    case (MiniScalaIntBitwiseAnd,       Seq(IntLit(x), IntLit(y)))  => IntLit(x & y)
    case (MiniScalaIntBitwiseOr,        Seq(IntLit(x), IntLit(y)))   => IntLit(x | y)
    case (MiniScalaIntBitwiseXOr,       Seq(IntLit(x), IntLit(y)))  => IntLit(x ^ y)

  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {

    case (MiniScalaIntP,  Seq(IntLit(_)))             => true
    case (MiniScalaIntP,  Seq(_))                     => false
    case (MiniScalaCharP, Seq(CharLit(_)))            => true
    case (MiniScalaCharP, Seq(_))                     => false
    case (MiniScalaBoolP, Seq(BooleanLit(_)))         => true
    case (MiniScalaBoolP, Seq(_))                     => false
    case (MiniScalaUnitP, Seq(UnitLit))               => true
    case (MiniScalaUnitP, Seq(_))                     => false
    case (MiniScalaIntLt, Seq(IntLit(x), IntLit(y)))  => x < y
    case (MiniScalaIntGe, Seq(IntLit(x), IntLit(y)))  => x >= y
    case (MiniScalaIntGt, Seq(IntLit(x), IntLit(y)))  => x > y
    case (MiniScalaIntLe, Seq(IntLit(x), IntLit(y)))  => x <= y
    case (MiniScalaEq,    Seq(IntLit(x), IntLit(y)))  => x == y
    case (MiniScalaNe,    Seq(IntLit(x), IntLit(y)))  => x != y

    case (MiniScalaEq,    Seq(BooleanLit(x), BooleanLit(y)))  => x == y
    case (MiniScalaNe,    Seq(BooleanLit(x), BooleanLit(y)))  => x != y

  }
}

object CPSOptimizerLow extends CPSOptimizer(SymbolicCPSTreeModuleLow)
    with (SymbolicCPSTreeModuleLow.Tree => SymbolicCPSTreeModuleLow.Tree) {
  import treeModule._

  protected val impure: ValuePrimitive => Boolean =
    Set(CPSBlockSet, CPSByteRead, CPSByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case CPSBlockAlloc(_) | CPSBlockGet | CPSByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case CPSBlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = CPSBlockTag
  protected val blockGet: ValuePrimitive = CPSBlockGet
  protected val blockSet: ValuePrimitive = CPSBlockSet
  protected val blockLength: ValuePrimitive = CPSBlockLength

  protected val identity: ValuePrimitive = CPSId

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSAdd), (1, CPSMul), (~0, CPSAnd), (0, CPSOr), (0, CPSXOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((CPSAdd, 0), (CPSSub, 0), (CPSMul, 1), (CPSDiv, 1),
        (CPSArithShiftL, 0), (CPSArithShiftR, 0),
        (CPSAnd, ~0), (CPSOr, 0), (CPSXOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSMul), (0, CPSAnd), (~0, CPSOr))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((CPSMul, 0), (CPSAnd, 0), (CPSOr, ~0))

  protected val sameArgReduce: Map[ValuePrimitive, Literal] =
    Map(CPSSub -> 0, CPSDiv -> 1, CPSMod -> 0, CPSXOr -> 0)

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case CPSLe | CPSGe | CPSEq => true
    case CPSLt | CPSGt | CPSNe => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
                                            Literal] = {
    case (CPSAdd, Seq(x, y)) => x + y
    case (CPSSub, Seq(x, y)) => x - y
    case (CPSMul, Seq(x, y)) => x * y
    case (CPSDiv, Seq(x, y)) if (y != 0) => Math.floorDiv(x, y)
    case (CPSMod, Seq(x, y)) if (y != 0) => Math.floorMod(x, y)

    case (CPSArithShiftL, Seq(x, y)) => x << y
    case (CPSArithShiftR, Seq(x, y)) => x >> y
    case (CPSAnd, Seq(x, y)) => x & y
    case (CPSOr, Seq(x, y)) => x | y
    case (CPSXOr, Seq(x, y)) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
                                            Boolean] = {

    case (CPSLt, Seq(x, y)) => x < y
    case (CPSLe, Seq(x, y)) => x <= y
    case (CPSEq, Seq(x, y)) => x == y
    case (CPSNe, Seq(x, y)) => x != y
    case (CPSGe, Seq(x, y)) => x >= y
    case (CPSGt, Seq(x, y)) => x > y
  }
}
