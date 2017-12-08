package miniscala

import miniscala.{ SymbolicCMScalaTreeModule => S }
import miniscala.{ SymbolicCPSTreeModule => C }

object CMScalaToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree = {
    nonTail(tree){_ =>
      val z = Symbol.fresh("c0")
      C.LetL(z, IntLit(0), C.Halt(z))
    }(Set.empty)
  }

  private def nonTail(tree: S.Tree)(ctx: Symbol=>C.Tree)(implicit mut: Set[Symbol]): C.Tree = {
    // @unchecked to avoid bogus compiler warnings

     (tree: @unchecked) match {

      case S.Let(name, _, value, body) =>
        nonTail(value)(v =>
            C.LetP(name, MiniScalaId, Seq(v), nonTail(body)(ctx)))

      // TODO: complete the following cases and add the missing ones.

      case S.Lit(x) =>
        val z = Symbol.fresh("lit") 
        C.LetL(z, x, ctx(z))

      case S.Prim(op, args) =>
        val res = op match {
          case op : MiniScalaValuePrimitive =>
            val z = Symbol.fresh("val_prim")
            nonTail_*(args)(v => (
              C.LetP(z, op, v, ctx(z))
            ))

          case op : MiniScalaTestPrimitive =>
            nonTail(
              S.If( S.Prim(op, args), S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false)))
              )(v => (
                  ctx(v)
                )  
              )
        }
        res

      // Reference of an immutable variable
      case S.Ref(name) if !mut(name) =>
        ctx(name)

      // Reference of an mutable variable
      case S.Ref(name) => // if mut(name) =>
        val z = Symbol.fresh("m_ref")
        val i = Symbol.fresh("index")

        val eval = C.LetP(z, MiniScalaBlockGet, Seq(name, i), ctx(z))
        C.LetL(i, IntLit(0), eval)

      case S.VarDec(name, _, rhs, body) =>
        val nmut = mut + name // add name to set of mutables
        val s = Symbol.fresh("size")
        val i = Symbol.fresh("index")
        val d = Symbol.fresh("dummy")

        val eval = nonTail(rhs)(v => (
          C.LetP(d, MiniScalaBlockSet, Seq(name, i, v), nonTail(body)(ctx)(nmut))
        ))

        val index = C.LetL(i, IntLit(0), eval)
        val block = C.LetP(name, MiniScalaBlockAlloc(242), Seq(s), index)
        C.LetL(s, IntLit(1), block)
      
      case S.VarAssign(name, rhs) => 
        val i = Symbol.fresh("index")
        val d = Symbol.fresh("dummy")

        val eval = nonTail(rhs)(v => (
          C.LetP(d, MiniScalaBlockSet, Seq(name, i, v), ctx(v))
        ))
        C.LetL(i, IntLit(0), eval)

      case S.If(cond, tBranch, eBranch) =>
        val c = Symbol.fresh("cont_tail")
        val x = Symbol.fresh("arg")
        val cont_tail = C.CntDef(c, Seq(x), ctx(x))

        val tName = Symbol.fresh("cont")
        val eName = Symbol.fresh("cont")


        //define continuation functions
        val ct = C.CntDef(tName, Seq(), tail(tBranch, c))
        val ce = C.CntDef(eName, Seq(), tail(eBranch, c))

        //evaluate condition  
        val eval = this.cond(cond, tName, eName)
        C.LetC(Seq(cont_tail), C.LetC(Seq(ct), C.LetC(Seq(ce), eval)))

      case S.While(cond, lbody, body) =>
        val cont = Symbol.fresh("cont")
        val loop = Symbol.fresh("loop")
        val lbodyc = Symbol.fresh("lbody")
        val bodyc = Symbol.fresh("body")
        val f = Symbol.fresh("false")

        //define continuation functions
        val c = C.CntDef(bodyc, Seq(), nonTail(body)(ctx))
        val ct = C.CntDef(lbodyc, Seq(), tail(lbody, loop))

        //if condition is true, loop else execute body
        val eval = this.cond(cond, lbodyc, bodyc)

        //setting f = false and calling eval
        val fals = C.LetL(f, BooleanLit(false), eval)
        
        //definition of the loop continuation function
        val d = Symbol.fresh("d")
        val loopc = C.CntDef(loop, Seq(d), fals)

        val a = Symbol.fresh("d")
        C.LetL(a, UnitLit, C.LetC(Seq(loopc, ct, c), C.AppC(loop, Seq(a))))

      case S.LetRec(funs, body) =>
        val funDefs = funs.map { f =>
            val retc = Symbol.fresh("retC_funDef")
            var argNames = f.args.map { case S.Arg(name, _, _) => name}
            
            C.FunDef(f.name, retc, argNames,
                tail(f.body, retc)
            )
        }

        val eval = nonTail(body)(v => (
          ctx(v)
        ))

        C.LetF(funDefs, eval)

      case S.App(f, _, args) =>
        val n = Symbol.fresh("retC_app")
        val x = Symbol.fresh("new_arg")
        val retC = C.CntDef(n, Seq(x), ctx(x))

        val eval = nonTail(f)(fun =>
            nonTail_*(args)(v => (
              C.AppF(fun, n, v)
            ))
        )

        C.LetC(Seq(retC), eval)
    }
  }

  private def nonTail_*(trees: Seq[S.Tree])(ctx: Seq[Symbol]=>C.Tree)(implicit mut: Set[Symbol]): C.Tree =
    trees match {
      case Seq() =>
        ctx(Seq())
      case t +: ts =>
        nonTail(t)(tSym => nonTail_*(ts)(tSyms => ctx(tSym +: tSyms)))
    }

  private def tail(tree: S.Tree, c: Symbol)(implicit mut: Set[Symbol]): C.Tree = {
    // @unchecked to avoid bogus compiler warnings
    (tree: @unchecked) match {
      case S.Let(name, _, value, body) =>
        nonTail(value)(v =>
          C.LetP(name, MiniScalaId, Seq(v), tail(body, c)))

      case S.Lit(x) =>
        val z = Symbol.fresh("lit") 
        C.LetL(z, x, C.AppC(c, Seq(z)))

      case S.Prim(op, args) =>
        val res = op match {
          case op : MiniScalaValuePrimitive =>
            val z = Symbol.fresh("val_prim")
            nonTail_*(args)(v => (
              C.LetP(z, op, v, C.AppC(c, Seq(z)))
            ))

          case op : MiniScalaTestPrimitive =>
            nonTail(
              S.If( S.Prim(op, args), S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false)))
              )(v => (
                  C.AppC(c, Seq(v))
                )  
              )
        }
        res

      // Reference of an immutable variable
      case S.Ref(name) if !mut(name) =>
        C.AppC(c, Seq(name))

      // Reference of an mutable variable
      case S.Ref(name) => // if mut(name) =>
        val z = Symbol.fresh("m_ref")
        val i = Symbol.fresh("index")

        val eval = C.LetP(z, MiniScalaBlockGet, Seq(name, i), C.AppC(c, Seq(z)))
        C.LetL(i, IntLit(0), eval)
      // TODO: add the missing cases.

      case S.VarDec(name, _, rhs, body) =>
        val nmut = mut + name // add name to set of mutables
        val s = Symbol.fresh("size")
        val i = Symbol.fresh("index")
        val d = Symbol.fresh("dummy")

        val eval = nonTail(rhs)(v => (
          C.LetP(d, MiniScalaBlockSet, Seq(name, i, v), tail(body, c)(nmut))
        ))

        val index = C.LetL(i, IntLit(0), eval)
        val block = C.LetP(name, MiniScalaBlockAlloc(242), Seq(s), index)
        C.LetL(s, IntLit(1), block)

      case S.VarAssign(name, rhs) => 
        val i = Symbol.fresh("index")
        val d = Symbol.fresh("dummy")

        val eval = nonTail(rhs)(v => (
          C.LetP(d, MiniScalaBlockSet, Seq(name, i, v), C.AppC(c, Seq(v)))
        ))
        C.LetL(i, IntLit(0), eval)
      
      case S.If(cond, tBranch, eBranch) =>
        val tName = Symbol.fresh("cont")
        val eName = Symbol.fresh("cont")

        //define continuation functions
        val ct = C.CntDef(tName, Seq(), tail(tBranch, c))
        val ce = C.CntDef(eName, Seq(), tail(eBranch, c))

        //evaluate condition  
        val eval = this.cond(cond, tName, eName)
        C.LetC(Seq(ct, ce), eval)
      
      case S.While(cond, lbody, body) =>
        val cont = Symbol.fresh("cont")
        val loop = Symbol.fresh("loop")
        val lbodyc = Symbol.fresh("lbody")
        val bodyc = Symbol.fresh("body")

        // define continuation functions
        val ct = C.CntDef(lbodyc, Seq(), tail(lbody, loop))
        // val ct = C.CntDef(lbodyc, Seq(), tail(lbody, loop))
        val b = C.CntDef(bodyc, Seq(), tail(body, c))

        val eval = this.cond(cond, lbodyc, bodyc)
 
        //definition of the loop continuation function
        val f = Symbol.fresh("d") 
        val loopc = C.CntDef(loop, Seq(f), eval)

        val d = Symbol.fresh("d")
        val s = C.LetC(Seq(loopc, b, ct), C.AppC(loop, Seq(d)))
        
        C.LetL(d, UnitLit, s)
      
      case S.LetRec(funs, body) =>
        val funDefs = funs.map { f =>
            val retc = Symbol.fresh("retC_funDef")
            var argNames = f.args.map { case S.Arg(name, _, _) => name}
            
            C.FunDef(f.name, retc, argNames, tail(f.body, retc))
        }

        val eval = tail(body, c)
        C.LetF(funDefs, eval)

      case S.App(f, _, args) =>
        nonTail(f)(fun =>
            nonTail_*(args)(v => (
              C.AppF(fun, c, v)
            ))
        ) 
    }
  }

  private def cond(tree: S.Tree, trueC: Symbol, falseC: Symbol)(implicit mut: Set[Symbol]): C.Tree = {
    implicit val pos = tree.pos

    def litToCont(l: CMScalaLiteral): Symbol =
      if (l != BooleanLit(false)) trueC else falseC

    tree match {

      case S.If(condE, S.Lit(tl), S.Lit(fl)) => 
          cond(condE, litToCont(tl), litToCont(fl))

      case S.If(condE, x: S.Tree, S.Lit(fl)) => 
        tempLetC("ac", Seq(), cond(x, trueC, falseC))(name => (
          cond(condE, name, litToCont(fl)))
        )

      case S.If(condE, S.Lit(tl), x: S.Tree) => 
        tempLetC("ac", Seq(), cond(x, trueC, falseC))(name => (
          cond(condE, litToCont(tl), name))
        )

      case S.Prim(p: MiniScalaTestPrimitive, args) =>
        nonTail_*(args)(as => C.If(p, as, trueC, falseC))

      case other =>
        nonTail(other)(o =>
          nonTail(S.Lit(BooleanLit(false)))(n =>
            C.If(MiniScalaNe, Seq(o, n), trueC, falseC)))
    }
  }

  private def tempLetC(cName: String, args: Seq[C.Name], cBody: C.Tree)
                      (body: C.Name=>C.Tree): C.Tree = {
    val cSym = Symbol.fresh(cName)
    C.LetC(Seq(C.CntDef(cSym, args, cBody)), body(cSym))
  }
}
