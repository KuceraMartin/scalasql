package scalasql.core

/**
 * A SQL query with interpolated `?`s expressions and the associated
 * interpolated values, of type [[Interp]]. Accumulates SQL snippets, parameters,
 * and referenced expressions in a tree structure to minimize copying overhead,
 * until [[SqlStr.flatten]] is called to convert it into a [[SqlStr.Flattened]]
 */
class SqlStr(
    private val queryParts: collection.IndexedSeq[CharSequence],
    private val params: collection.IndexedSeq[SqlStr.Interp],
    val isCompleteQuery: Boolean,
    private val referencedExprs: collection.IndexedSeq[Expr.Identity]
) extends SqlStr.Renderable {
  def +(other: SqlStr) = {
    new SqlStr(
      SqlStr.plusParts,
      Array[SqlStr.Interp](this, other),
      false,
      SqlStr.emptyIdentityArray
    )
  }

  def withCompleteQuery(v: Boolean) = new SqlStr(queryParts, params, v, referencedExprs)
  override def toString = SqlStr.flatten(this).renderSql(false)

  override protected def renderSql(ctx: Context): SqlStr = this
}

object SqlStr {
  private val emptyIdentityArray = Array.empty[Expr.Identity]
  private val plusParts: IndexedSeq[String] = Array("", "", "")

  /**
   * Represents a [[SqlStr]] that has been flattened out into a single set of
   * parallel arrays, allowing you to render it or otherwise make use of its data.
   */
  class Flattened(
      val queryParts: collection.IndexedSeq[CharSequence],
      val params: collection.IndexedSeq[Interp.TypeInterp[_]],
      isCompleteQuery: Boolean,
      val referencedExprs: collection.IndexedSeq[Expr.Identity]
  ) extends SqlStr(queryParts, params, isCompleteQuery, referencedExprs){
    def renderSql(castParams: Boolean) = {
      val queryStr = queryParts.iterator
        .zipAll(params, "", null)
        .map {
          case (part, null) => part
          case (part, param) =>
            val jdbcTypeString = param.mappedType.castTypeString
            if (castParams) part + s"CAST(? AS $jdbcTypeString)" else part + "?"
        }
        .mkString

      queryStr
    }

  }

  /**
   * Helper method turn an `Option[T]` into a [[SqlStr]], returning
   * the empty string if the `Option` is `None`
   */
  def opt[T](t: Option[T])(f: T => SqlStr) = t.map(f).getOrElse(SqlStr.empty)

  /**
   * Helper method turn an `Seq[T]` into a [[SqlStr]], returning
   * the empty string if the `Seq` is empty
   */
  def optSeq[T](t: Seq[T])(f: Seq[T] => SqlStr) = if (t.nonEmpty) f(t) else SqlStr.empty

  /**
   * Flattens out a [[SqlStr]] into a single flattened [[SqlStr.Flattened]] object,
   * at which point you can use its `queryParts`, `params`, `referencedExprs`, etc.
   */
  def flatten(self: SqlStr): Flattened = {
    // Implement this in a mutable style because`it's pretty performance sensitive
    val finalParts = collection.mutable.ArrayBuffer.empty[StringBuilder]
    val finalArgs = collection.mutable.ArrayBuffer.empty[Interp.TypeInterp[_]]
    val finalExprs = collection.mutable.ArrayBuffer.empty[Expr.Identity]
    // Equivalent to `finalParts.last`, cached locally for performance
    var lastFinalPart: StringBuilder = null

    def rec(self: SqlStr, topLevel: Boolean): Unit = {
      val queryParts = self.queryParts
      val params = self.params
      finalExprs.appendAll(self.referencedExprs)
      var boundary = true
      val parenthesize = !topLevel && self.isCompleteQuery
      if (parenthesize) addFinalPart("(")
      boundary = true

      def addFinalPart(s: CharSequence) = {
        if (boundary && finalParts.nonEmpty) {
          finalParts.last.append(s)
        } else {
          lastFinalPart = new StringBuilder()
          lastFinalPart.append(s)
          finalParts.append(lastFinalPart)
        }
      }

      var i = 0
      val length = params.length
      while (i < length) {
        val p = queryParts(i)
        val a = params(i)
        addFinalPart(p)
        boundary = false
        a match {
          case si: Interp.SqlStrInterp =>
            rec(si.s, false)
            boundary = true

          case s: Interp.TypeInterp[_] => finalArgs.append(s)
        }
        i += 1
      }

      addFinalPart(queryParts(queryParts.length - 1))
      if (parenthesize) addFinalPart(")")
    }

    rec(self, true)
    new Flattened(finalParts, finalArgs, self.isCompleteQuery, finalExprs)
  }

  /**
   * Provides the sql"..." syntax for constructing [[SqlStr]]s
   */
  implicit class SqlStringSyntax(sc: StringContext) {
    def sql(args: Interp*) =
      new SqlStr(sc.parts.toIndexedSeq, args.toIndexedSeq, false, Array.empty[Expr.Identity])
  }

  /**
   * Joins a `Seq` of [[SqlStr]]s into a single [[SqlStr]] using the given [[sep]] separator
   */
  def join(strs: IterableOnce[SqlStr], sep: SqlStr = empty): SqlStr = {
    strs.iterator.reduceOption(_ + sep + _).getOrElse(empty)
  }

  lazy val empty = sql""
  lazy val commaSep = sql", "

  /**
   * Converts a raw `String` into a [[SqlStr]]. Note that this must be used
   * carefully to avoid SQL injection attacks.
   */
  def raw(s: String, referencedExprs: Array[Expr.Identity] = Array.empty) =
    new SqlStr(Array(s), Array.empty[SqlStr.Interp], false, referencedExprs)

  trait Renderable {
    protected def renderSql(ctx: Context): SqlStr
  }

  object Renderable {
    def renderSql(x: Renderable)(implicit ctx: Context) = x.renderSql(ctx)
  }

  /**
   * Something that can be interpolated into a [[SqlStr]].
   */
  sealed trait Interp
  object Interp {
    implicit def renderableInterp(t: Renderable)(implicit ctx: Context): Interp =
      SqlStrInterp(Renderable.renderSql(t)(ctx))

    implicit def sqlStrInterp(s: SqlStr): Interp = SqlStrInterp(s)

    case class SqlStrInterp(s: SqlStr) extends Interp

    implicit def typeInterp[T: TypeMapper](value: T): Interp = TypeInterp(value)
    case class TypeInterp[T: TypeMapper](value: T) extends Interp {
      def mappedType: TypeMapper[T] = implicitly[TypeMapper[T]]
    }
  }
}
