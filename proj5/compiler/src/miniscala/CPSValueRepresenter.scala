package miniscala

import BitTwiddling.bitsToIntMSBF
import miniscala.{ SymbolicCPSTreeModule => H }
import miniscala.{ SymbolicCPSTreeModuleLow => L }

/**
 * Value-representation phase for the CPS language. Translates a tree
 * with high-level values (blocks, integers, booleans, unit) and
 * corresponding primitives to one with low-level values (blocks
 * and integers only) and corresponding primitives.
 *
 * @author Michel Schinz <Michel.Schinz@epfl.ch>
 */

object CPSValueRepresenter extends (H.Tree => L.Tree) {
  def apply(tree: H.Tree): L.Tree =
    transform(tree)(Map.empty)

  private def transform(tree: H.Tree)
                       (implicit worker: Map[Symbol, (Symbol, Seq[Symbol])])
      : L.Tree = tree match {

    // Literals
    case H.LetL(name, IntLit(value), body) =>
      L.LetL(name, (value << 1) | 1, transform(body))
    case H.LetL(name, CharLit(value), body) =>
      L.LetL(name, (value << 3) | bitsToIntMSBF(1, 1, 0), transform(body))

    // TODO: Add missing literals
    case H.LetL(name, BooleanLit(true), body) =>
      L.LetL(name, 26, transform(body))

    case H.LetL(name, BooleanLit(false), body) =>
      L.LetL(name, 10, transform(body))

    case H.LetL(name, UnitLit, body) => 
      L.LetL(name, 2, transform(body))

    // *************** Primitives ***********************
    // Make sure you implement all possible primitives
    // (defined in MiniScalaPrimitives.scala)
    //
    // Integer primitives
    case H.LetP(name, MiniScalaIntAdd, args, body) =>
      tempLetP(CPSAdd, args) { r =>
        tempLetL(1) { c1 =>
          L.LetP(name, CPSSub, Seq(r, c1), transform(body)) } }

    // TODO: Add missing integer primitives
    case H.LetP(name, MiniScalaIntSub, Seq(arg), body) => 
      val z = Symbol.fresh("z")
      transform(H.LetL(z, IntLit(0), H.LetP(name, MiniScalaIntSub, Seq(z, arg), body)))

    case H.LetP(name, MiniScalaIntSub, args, body) => 
      tempLetP(CPSSub, args) { r=> 
      tempLetL(1) { c1 =>
          L.LetP(name, CPSAdd, Seq(r, c1), transform(body)) } }

    case H.LetP(name, MiniScalaIntMul, Seq(arg1, arg2), body) => 
      tempLetL(1) { one =>
        tempLetP(CPSSub, Seq(arg1, one)) { lhs1 =>
          tempLetP(CPSArithShiftR, Seq(arg2, one)){ lhs2 => 
            tempLetP(CPSMul, Seq(lhs1, lhs2))( lhs3 => 
              L.LetP(name, CPSAdd, Seq(lhs3, one), transform(body))
            )
          }
        }
      }

    case H.LetP(name, MiniScalaIntDiv, Seq(n, m), body) => 
      tempLetL(1)(c1 => (
        tempLetP(CPSSub, Seq(n, c1))(t1 => (
          tempLetP(CPSArithShiftR, Seq(m, c1))(t2 => (
            tempLetP(CPSDiv, Seq(t1, t2))(t3 => (
                L.LetP(name, CPSAdd, Seq(t3, c1), transform(body))
            ))
          ))
        ))
      ))

    case H.LetP(name, MiniScalaIntMod, Seq(n, m), body) => 
      tempLetL(1)(c1 => (
        tempLetP(CPSArithShiftR, Seq(n, c1))(t1 => (
          tempLetP(CPSArithShiftR, Seq(m, c1))(t2 => (
            tempLetP(CPSMod, Seq(t1, t2))(t3 => (
              tempLetL(2)(c2 => (
                tempLetP(CPSMul, Seq(t3, c2))(t4 => (
                  L.LetP(name, CPSAdd, Seq(t4, c1), transform(body))
                ))
              ))
            ))
          ))
        ))
      ))

    case H.LetP(name, MiniScalaIntBitwiseAnd, Seq(n, m), body) => 
      L.LetP(name, CPSAnd, Seq(n, m), transform(body))

    case H.LetP(name, MiniScalaIntBitwiseOr, Seq(n, m), body) => 
      L.LetP(name, CPSOr, Seq(n, m), transform(body))

    case H.LetP(name, MiniScalaIntBitwiseXOr, Seq(n, m), body) => 

      tempLetL(1)(c => (
        tempLetP(CPSXOr, Seq(n, m))(t1 => (
          L.LetP(name, CPSOr, Seq(t1, c), transform(body)) 
        ))  
      )) 
      
    case H.LetP(name, MiniScalaIntArithShiftLeft, Seq(n, m), body) => 
      tempLetL(1)(c1 => (
        tempLetP(CPSArithShiftR, Seq(n, c1))(t1 => (
          tempLetP(CPSArithShiftR, Seq(m, c1))(t2 => (
            tempLetP(CPSArithShiftL, Seq(t1, t2))(t3 => (
              tempLetL(2)(c2 => (
                tempLetP(CPSMul, Seq(t3, c2))(t4 => (
                  L.LetP(name, CPSAdd, Seq(t4, c1), transform(body))
                ))
              ))
            ))
          ))
        ))
      ))  

      case H.LetP(name, MiniScalaIntArithShiftRight, Seq(n, m), body) => 
      tempLetL(1)(c1 => (
        tempLetP(CPSArithShiftR, Seq(n, c1))(t1 => (
          tempLetP(CPSArithShiftR, Seq(m, c1))(t2 => (
            tempLetP(CPSArithShiftR, Seq(t1, t2))(t3 => (
              tempLetL(2)(c2 => (
                tempLetP(CPSMul, Seq(t3, c2))(t4 => (
                  L.LetP(name, CPSAdd, Seq(t4, c1), transform(body))
                ))
              ))
            ))
          ))
        ))
      )) 

    // Block primitives
    // TODO: Add block primitives
    case H.LetP(name, MiniScalaBlockAlloc(t), Seq(s), body) => 
      tempLetL(1)(r => (
        tempLetP(CPSArithShiftR, Seq(s, r))(v => (
          L.LetP(name, CPSBlockAlloc(t), Seq(v), transform(body))
        ))
      ))

    case H.LetP(name, MiniScalaBlockGet, Seq(n1, i), body) =>
      tempLetL(1)(c1 => (
        tempLetP(CPSArithShiftR, Seq(i, c1))(t1 =>(
            L.LetP(name, CPSBlockGet, Seq(n1, t1), transform(body)) 
          )) 
        ))

    case H.LetP(name, MiniScalaBlockSet, Seq(n1, i, v), body) =>
      tempLetL(1)(c1 => (
        tempLetP(CPSArithShiftR, Seq(i, c1))(t1 => (
          tempLetP(CPSBlockSet, Seq(n1, t1, v))(t2 =>(
            L.LetL(name, 2, transform(body))
          ))
        ))
      ))

    case H.LetP(name, MiniScalaBlockTag, Seq(n1), body) => 
      tempLetL(1)(c1 => (
        tempLetP(CPSBlockTag, Seq(n1))(t1 => (
          tempLetP(CPSArithShiftL, Seq(t1, c1))(t2 => (
            L.LetP(name, CPSAdd, Seq(t2, c1), transform(body))
          ))
        ))
      ))

    case H.LetP(name, MiniScalaBlockLength, Seq(s), body) => 
      tempLetL(1)(c1 => (
        tempLetP(CPSBlockLength, Seq(s))(t1 => (
          tempLetP(CPSArithShiftL, Seq(t1, c1))(t2 => (
            L.LetP(name, CPSOr, Seq(t2, c1), transform(body))
          ))
        ))
      ))

    // Conversion primitives int->char/char->int
    // TODO
    case H.LetP(name, MiniScalaCharToInt, Seq(n1), body) =>
      tempLetL(2)(c2 => (
        L.LetP(name, CPSArithShiftR, Seq(n1, c2), transform(body))
      ))

    case H.LetP(name, MiniScalaIntToChar, Seq(n1), body) =>
      tempLetL(2)(c2 => (
        tempLetP(CPSArithShiftL, Seq(n1, c2))(t1 => (
          L.LetP(name, CPSAdd, Seq(t1, c2),transform(body))
        ))
      ))

    // IO primitives
    // TODO
    case H.LetP(name, MiniScalaByteRead, Seq(), body) =>
      tempLetP(CPSByteRead, Seq())(t1 => (
        tempLetL(1)(c1 => (
          tempLetP(CPSArithShiftL, Seq(t1, c1))(t2 => (
            L.LetP(name, CPSAdd, Seq(t2, c1), transform(body))
          ))
        ))
      ))

    case H.LetP(name, MiniScalaByteWrite, Seq(n1), body) =>
      tempLetL(1)(c1 => (
        tempLetP(CPSArithShiftR, Seq(n1, c1))(t1 => (
          tempLetP(CPSByteWrite, Seq(t1))(t2 => (
            L.LetL(name, 2, transform(body))
          ))
        ))
      ))
     
    // Other primitives
    // TODO
    case H.LetP(name, MiniScalaId, Seq(i), body) => 
      L.LetP(name, CPSId, Seq(i), transform(body))

    case H.If(MiniScalaIntP, Seq(n), ct, cf) => 
      tempLetL(1)(c1 => (
        tempLetP(CPSAnd, Seq(n, c1))(t1 => (
          L.If(CPSEq, Seq(t1, c1), ct, cf)
        ))
      ))

    case H.If(MiniScalaBoolP, Seq(n), ct, cf) => 
      tempLetL(15)(m => (   //1111
        tempLetL(10)(t => ( //1010
          tempLetP(CPSAnd, Seq(n, m))(t1 => (
            L.If(CPSEq, Seq(t1, t), ct, cf)
          ))
        ))
      ))

    case H.If(MiniScalaUnitP, Seq(n), ct, cf) => 
      tempLetL(15)(m => (   //1111
        tempLetL(2)(t => (  //0010
          tempLetP(CPSAnd, Seq(n, m))(t1 => (
            L.If(CPSEq, Seq(t1, t), ct, cf)
          ))
        ))
      ))

    case H.If(MiniScalaCharP, Seq(n), ct, cf) => 
      tempLetL(6)(c6 => (
        tempLetP(CPSAnd, Seq(n, c6))(t1 => (
          L.If(CPSEq, Seq(t1, c6), ct, cf)
        ))
      ))

    // Continuations nodes (LetC, AppC)
    // TODO
    case H.LetC(funs, body) => 
      val nfuns = funs map {
        case H.CntDef(name, args, body) => 
          L.CntDef(name, args, transform(body))
        }
      L.LetC(nfuns, transform(body))

    case H.AppC(name, args) => 
       L.AppC(name, args)

    // Functions nodes (LetF, AppF)
    // TODO
    case H.LetF(funs, body) => 
      val dum = Symbol.fresh("dummy")
      var workers = List(dum)
      var fnames = List(dum)
      var lengths = List(1)
      var fvs = List(List(dum))

      val nfuns = funs map {
        case f@H.FunDef(name, retC, args, fbody) => 
          
          val fv = (freeVariables(f)(Map.empty)).toList
          val env = Symbol.fresh("env")
          val w = Symbol.fresh("w")

          workers = w :: workers
          fnames = name :: fnames
          lengths = (fv.length + 1) :: lengths
          fvs = fv :: fvs

          var j = 0;
          var fv_names = List[miniscala.Symbol]();

          while(j < fv.length) {
            fv_names = Symbol.fresh("FV") :: fv_names
            j += 1
          }
          val subs = Substitution(name +: fv , env +: fv_names)
          var res = transform(fbody).subst(subs)
          var i = fv.length; 
          
          while(i > 0) {
            res = tempLetL(i)(c => (
              L.LetP(fv_names(i - 1), CPSBlockGet, Seq(env, c), res)
            ))
            i -= 1;
          } 

          L.FunDef(w, retC, Seq(env) ++ args, res)    
      }
      
      var res2 = transform(body)

      var i = 0;
      var j = 0;
      while(i < fvs.length - 1) {
        res2 = tempLetL(0)(z => (
           L.LetP(Symbol.fresh("t"), CPSBlockSet, Seq(fnames(i), z, workers(i)), res2)
        ))
        j = 0
        while(j < fvs(i).length) {
          res2 = tempLetL(j + 1)(idx => (
            L.LetP(Symbol.fresh("t"), CPSBlockSet, Seq(fnames(i), idx, fvs(i)(j)), res2)
          ))
          j += 1
        }
        i += 1
      }

      i = 0;
      while(i < workers.length - 1) {
        res2 = tempLetL(lengths(i))(l => (
          L.LetP(fnames(i), CPSBlockAlloc(202), Seq(l), res2)
        ))
        i += 1;
      }
      L.LetF(nfuns, res2)

    case H.AppF(name, ret, args) => 
      tempLetL(0)(c => (
        tempLetP(CPSBlockGet, Seq(name, c))(f => (
          L.AppF(f, ret, name +: args)
        ))
      ))
      // L.AppF(name, ret, args)

    // ********************* Conditionnals ***********************
    // Type tests
    case H.If(MiniScalaBlockP, Seq(a), thenC, elseC) =>
      ifEqLSB(a, Seq(0, 0), thenC, elseC)
    // TODO: add missing cases

    // Test primitives (<, >, ==, ...)
     case H.If(op, args, ct, cf) =>
      var res = op match {
        case MiniScalaIntLt =>
          L.If(CPSLt, args, ct, cf)
        case MiniScalaIntLe =>
          L.If(CPSLe, args, ct, cf)
        case MiniScalaIntGe =>
          L.If(CPSGe, args, ct, cf)
        case MiniScalaIntGt =>
          L.If(CPSGt, args, ct, cf)
        case MiniScalaEq =>
          L.If(CPSEq, args, ct, cf)
        case MiniScalaNe => 
          L.If(CPSNe, args, ct, cf) 
      }
      res

    // TODO

    // Halt case
    case H.Halt(name) => 
      tempLetL(1) ( r =>
        tempLetP(CPSArithShiftR, Seq(name, r)) (v => (
          L.Halt(v)
        ))
      )
  }

  /**
   * Auxilary function.
   *
   * Example:
   *  // assuming we have a function with symbol f and the return continuation is rc:
   *
   *  val names = Seq("first", "second")
   *  val values = Seq(42, 112)
   *  val inner = L.AppF(f, rc, names)
   *  val res = wrap(names zip values , inner) {
   *    case ((n, v), inner) => L.LetL(n, v, inner)
   *  }
   *
   *  // res is going to be the following L.Tree
   *  L.LetL("first", 42,
   *    L.LetL("second", 112,
   *      L.AppF(f, rc, Seq("first", "second"))
   *    )
   *  )
   */
  private def wrap[T](args: Seq[T], inner: L.Tree)(addOneLayer: (T, L.Tree) => L.Tree) = {
    def addLayers(args: Seq[T]): L.Tree = args match {
      case h +: t => addOneLayer(h, addLayers(t))
      case _ => inner
    }
    addLayers(args)
  }

  private def freeVariables(tree: H.Tree)
                           (implicit worker: Map[Symbol, Set[Symbol]])
      : Set[Symbol] = tree match {
    case H.LetL(name, _, body) =>
      freeVariables(body) - name
    case H.LetP(name, _, args, body) =>
      freeVariables(body) - name ++ args
    // TODO: add missing cases
    case H.LetC(funs, body) =>
      funs.foldLeft(freeVariables(body))((acc, cur) => cur match {
        case H.CntDef(name, args, fbody) => 
          acc ++ freeVariables(fbody) -- args
      })

    case H.LetF(funs, body) =>
      funs.foldLeft(freeVariables(body))((acc, cur) => cur match {
        case H.FunDef(name, retC, args, fbody) => 
          acc ++ freeVariables(fbody) -- args - name
      })
      
    case H.AppC(name, args) =>
      args.toSet
    case H.AppF(name, ret, args) =>
      args.toSet ++ Set(name)
    case H.If(op, args, ct, cf) =>
      args.toSet
  }

  private def freeVariables(cnt: H.CntDef)
                           (implicit worker: Map[Symbol, Set[Symbol]])
      : Set[Symbol] =
    freeVariables(cnt.body) - cnt.name -- cnt.args

  private def freeVariables(fun: H.FunDef)
                           (implicit worker: Map[Symbol, Set[Symbol]])
      : Set[Symbol] =
    freeVariables(fun.body) - fun.name -- fun.args

  // Tree builders

  /**
   * Call body with a fresh name, and wraps its resulting tree in one
   * that binds the fresh name to the given literal value.
   */
  private def tempLetL(v: Int)(body: L.Name => L.Tree): L.Tree = {
    val tempSym = Symbol.fresh("t")
    L.LetL(tempSym, v, body(tempSym))
  }

  /**
   * Call body with a fresh name, and wraps its resulting tree in one
   * that binds the fresh name to the result of applying the given
   * primitive to the given arguments.
   */
  private def tempLetP(p: L.ValuePrimitive, args: Seq[L.Name])
                      (body: L.Name => L.Tree): L.Tree = {
    val tempSym = Symbol.fresh("t")
    L.LetP(tempSym, p, args, body(tempSym))
  }

  /**
   * Generate an If tree to check whether the least-significant bits
   * of the value bound to the given name are equal to those passed as
   * argument. The generated If tree will apply continuation tC if it
   * is the case, and eC otherwise. The bits should be ordered with
   * the most-significant one first (e.g. the list (1,1,0) represents
   * the decimal value 6).
   */
  private def ifEqLSB(arg: L.Name, bits: Seq[Int], tC: L.Name, eC: L.Name)
      : L.Tree =
    tempLetL(bitsToIntMSBF(bits map { b => 1 } : _*)) { mask =>
      tempLetP(CPSAnd, Seq(arg, mask)) { masked =>
        tempLetL(bitsToIntMSBF(bits : _*)) { value =>
          L.If(CPSEq, Seq(masked, value), tC, eC) } } }
}
