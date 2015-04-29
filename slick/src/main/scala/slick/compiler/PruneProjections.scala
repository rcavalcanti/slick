package slick.compiler

import slick.ast._
import Util._
import TypeUtil._

/** Remove unreferenced fields from StructNodes and convert unreferenced
  * StructNodes to single columns or ProductNodes (which is needed for
  * aggregation functions and at the top level). */
class PruneProjections extends Phase {
  val name = "pruneProjections"

  def apply(state: CompilerState) = state.map { n => ClientSideOp.mapServerSide(n, true) { n =>
    val top = n.nodeType match {
      case CollectionType(_, NominalType(sym, _)) => sym
      case NominalType(sym, _) => sym
    }
    val referenced = n.collect[(TypeSymbol, Symbol)] { case Select(_ :@ NominalType(s, _), f) => (s, f) }.toSet
    val allTSyms = n.collect[TypeSymbol] { case Pure(_, _) :@ CollectionType(_, NominalType(ts, _)) => ts }.toSet
    val unrefTSyms = allTSyms -- referenced.map(_._1)
    logger.debug(s"Result tsym: $top; Unreferenced: ${unrefTSyms.mkString(", ")}; Field refs: ${referenced.mkString(", ")}")
    def tr(n: Node): Node =  n.replace {
      case (p @ Pure(s @ StructNode(ch), pts)) :@ CollectionType(_, NominalType(ts, _)) =>
        if(unrefTSyms contains ts) {
          val ch2 = s.nodeChildren.map(tr)
          val res = Pure(if(ch2.length == 1 && ts != top) ch2(0) else ProductNode(ch2), pts)
          res
        } else {
          val ch2 = ch.collect { case (sym, n) if referenced.contains((ts, sym)) => (sym, tr(n)) }
          if(ch2 == ch) p else Pure(StructNode(ch2), pts)
        }
    }
    tr(n)
  }}
}
