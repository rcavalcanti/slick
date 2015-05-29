package slick.compiler

import slick.ast.Library.AggregateFunctionSymbol
import slick.ast.TypeUtil._
import slick.ast.Util._
import slick.ast._
import slick.util.Ellipsis

/** Rewrite aggregation function calls to Aggregate nodes. */
class CreateAggregates extends Phase {
  val name = "createAggregates"

  def apply(state: CompilerState) = state.map(tr)

  def tr(n: Node): Node = n.nodeMapChildren(tr, keepType = true) match {
    case n @ Apply(f: AggregateFunctionSymbol, Seq(from)) :@ tpe =>
      logger.debug("Converting aggregation function application", n)
      val CollectionType(_, elType @ Type.Structural(StructType(els))) = from.nodeType
      val s = new AnonSymbol
      val ref = Select(Ref(s) :@ elType, els.head._1) :@ els.head._2
      val a = Aggregate(s, from, Apply(f, Seq(ref))(tpe)).nodeWithComputedType()
      logger.debug("Converted aggregation function application", a)
      inlineMap(a)

    case n => n
  }

  /** Recursively inline mapping Bind calls under an Aggregate */
  def inlineMap(a: Aggregate): Aggregate = a.from match {
    case Bind(s1, f1, Pure(StructNode(defs1), ts1)) =>
      logger.debug("Inlining mapping Bind under Aggregate", a)
      val defs1M = defs1.toMap
      val sel = a.select.replace({
        case FwdPath(s :: f :: rest) if s == a.sym =>
          rest.foldLeft(defs1M(f)) { case (n, s) => n.select(s) }.nodeWithComputedType()
      }, keepType = true)
      val a2 = Aggregate(s1, f1, sel) :@ a.nodeType
      logger.debug("Inlining mapping Bind under Aggregate", a2)
      inlineMap(a2)
    case _ => a
  }
}
