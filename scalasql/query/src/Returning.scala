package scalasql.query

import scalasql.core.SqlStr.{Renderable, SqlStringSyntax}
import scalasql.core.{Context, ExprsToSql, Queryable, SqlStr, TypeMapper, WithSqlExpr}
import scalasql.renderer.JoinsToSql

/**
 * A query that could support a `RETURNING` clause, typically
 * an `INSERT` or `UPDATE`
 */
trait Returnable[Q] extends Renderable with WithSqlExpr[Q] {
  def table: TableRef
}

trait InsertReturnable[Q] extends Returnable[Q]

/**
 * A query with a `RETURNING` clause
 */
trait Returning[Q, R] extends Query.Multiple[R] {
  def single: Query.Single[R] = new Query.Single(this)
}

object InsertReturning {
  class Impl[Q, R](returnable: InsertReturnable[_], returning: Q)(
      implicit val qr: Queryable.Row[Q, R]
  ) extends Returning.Impl0[Q, R](qr, returnable, returning)
      with Returning[Q, R] {
    protected def expr: Q = returning
  }
}
object Returning {
  class Impl0[Q, R](qr: Queryable.Row[Q, R], returnable: Returnable[_], returning: Q)
      extends Returning[Q, R] {

    override protected def queryConstruct(args: Queryable.ResultSetIterator): Seq[R] = {
      Seq(qr.construct(args))
    }

    protected def queryWalkLabels() = qr.walkLabels(returning)

    protected def queryWalkExprs() = qr.walkExprs(returning)

    override def queryIsSingleRow = false

    protected override def renderSql(ctx0: Context) = {
      implicit val implicitCtx = Context.compute(ctx0, Nil, Some(returnable.table))

      val prefix = Renderable.renderSql(returnable)
      val walked = qr.walkLabelsAndExprs(returning)
      val exprStr = ExprsToSql.apply(walked, implicitCtx, SqlStr.empty)
      val suffix = sql" RETURNING $exprStr"

      prefix + suffix
    }

  }
  class Impl[Q, R](returnable: Returnable[_], returning: Q)(implicit val qr: Queryable.Row[Q, R])
      extends Impl0[Q, R](qr, returnable, returning)
      with Returning[Q, R]

}
