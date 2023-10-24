package scalasql.query

import renderer.InsertToSql
import scalasql.renderer.{Context, SqlStr}
import scalasql.Queryable
import scalasql.utils.OptionPickler

/**
 * Syntax reference
 *
 * https://www.postgresql.org/docs/current/sql-update.html
 */
case class InsertSelect[Q, C, R, R2](insert: Insert[Q, R], columns: C, select: Select[C, R2])
    extends Returnable[Q] with Query[Int] {
  def expr = insert.expr
  def table = insert.table

  override def toSqlQuery(implicit ctx: Context) =
    InsertToSql.select(this, select.qr.walk(columns).map(_._2), ctx)

  override def isExecuteUpdate = true

  def walk() = Nil

  override def singleRow = true

  override def valueReader: OptionPickler.Reader[Int] = implicitly
}
