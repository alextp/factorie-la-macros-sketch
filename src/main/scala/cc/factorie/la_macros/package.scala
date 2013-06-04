package cc.factorie

import scala.language.experimental.macros
import scala.reflect.macros.Context
import cc.factorie.la.Tensor


package object la_macros {
  import cc.factorie.la._
  def fastTensorForeach(tensor: Tensor, f: (Int, Double) => Unit): Unit = macro impl


  def impl(c: Context)
          (tensor: c.Expr[Tensor], f: c.Expr[(Int, Double) => Unit] ): c.Expr[Unit] = {
    import c.universe._
    import definitions._
    import Flag._
    def block(trees: Tree*) = Block(trees.toList, Literal(Constant(())))
    def newVariable(n: String, definition: Tree, isConstant: Boolean = true) = {
      val name = c.fresh(n)
      (name, if (isConstant) {
        ValDef(Modifiers(), newTermName(name), TypeTree(), definition)
      } else {
        ValDef(Modifiers(MUTABLE), newTermName(name), TypeTree(), definition)
      })
    }
    def makeBody(intVar: Tree, doubleVar: Tree) = c.typeCheck(f.tree) match {
      case Function(List(i, d), body) =>
        val declareIdx = ValDef(NoMods, i.name, TypeTree(IntTpe), intVar)
        val declareVal = ValDef(NoMods, d.name, TypeTree(DoubleTpe), doubleVar)
        val bodyExpr = c.resetAllAttrs(body)
        block(declareIdx, declareVal, bodyExpr)
    }
    val tName = c.fresh("t")
    def Var(name: String) = Ident(newTermName(name))
    def While(cond: Tree, blk: Block) = {
      val cnd = c.Expr(cond)
      val bk = c.Expr(blk)
      reify {
        while (cnd.splice) { bk.splice }
      }
    }
    def callMethod0(obj: String, method: String) = Select(Var(obj), newTermName(method))
    def callMethod(obj: String, method: String, arg1: Tree) = Apply(Select(Var(obj), newTermName(method)), List(arg1))
    def incrementVariable(name: String) = {
      Assign(Var(name), callMethod(name, "$plus", Literal(Constant(1))))
    }
    val denseTensorBlock = {
      /* This should generate something like
       * var i = 0
       * val arr = t.asArray
       * while (i < arr.length) {
       *   val ii = i
       *   val v = arr(i)
       *   f(ii, v)
       *   i += 1
       * }
       */
      val (i, iDef) = newVariable("i", Literal(Constant(0)), isConstant=false)
      val (arr, arrDef) = newVariable("arr", callMethod0(tName, "asArray"))
      val (ii, iiDef) = newVariable("ii", Var(i))
      val (v, vDef) = newVariable("v", callMethod(arr, "apply", Var(i)))
      block(iDef, arrDef,
        While(callMethod(i, "$less", callMethod0(arr, "length")),
          block(iiDef, vDef, makeBody(Var(ii), Var(v)), incrementVariable(i))).tree)
    }
    val sparseTensorBlock: Tree = {
      /*
       * This should generate something like
       * var i = 0
       * val len = t.activeDomainSize
       * val indices = t._indices
       * val values = t._valuesSeq
       * while (i < len) {
       *   val idx = indices(i)
       *   val v = values(i)
       *   f(idx, v)
       *   i += 1
       * }
       */
      val (i, iDef) = newVariable("i", Literal(Constant(0)), isConstant=false)
      val (len,lenDef) = newVariable("len", callMethod0(tName, "activeDomainSize"))
      val (indices, indicesDef) = newVariable("indices", callMethod0(tName, "_indices"))
      val (values, valuesDef) = newVariable("values", callMethod0(tName, "_valuesSeq"))
      val (idx, idxDef) = newVariable("idx", callMethod(indices, "apply", Var(i)))
      val (v, vDef) = newVariable("v", callMethod(values, "apply", Var(i)))
      block(iDef, lenDef, indicesDef, valuesDef,
        While(callMethod(i, "$less", Var(len)),
          block(idxDef, vDef, makeBody(Var(idx), Var(v)), incrementVariable(i))).tree)
    }
    def makeCaseExpr(typeName: String, blk: Tree) = {
      /*
      * This should generate something like
      *   case t: typeName => block; ()
      * */
      CaseDef(
        Bind(newTermName(tName), Typed(Ident(nme.WILDCARD), Ident(newTypeName(typeName)))),
        EmptyTree,
        block(blk))
    }
    val de = makeCaseExpr("DenseTensor", denseTensorBlock)
    val se = makeCaseExpr("SparseTensor", sparseTensorBlock)
    /*
    * This should generate something like
    *   tensor match {
    *      ...
    *   }
    * with the above cases in place of ...
    * */
    val m = c.Expr(Match(tensor.tree, List(de, se)))
    reify {
      import cc.factorie.la._
      m.splice
    }
  }
}

