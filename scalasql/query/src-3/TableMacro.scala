package scalasql.query

import scala.quoted.*
import scalasql.query.Table.Metadata
import scalasql.core.DialectTypeMappers
import scalasql.core.Queryable
import scalasql.core.{Sc, TypeMapper}
import scalasql.core.{Expr => SqlExpr}
import scalasql.core.Queryable.Row
import scalasql.core.Queryable.ResultSetIterator

object TableMacros:

  def metadataImpl[V[_[_]] : Type](using Quotes): Expr[Table.Metadata[V]] =
    import quotes.reflect.*

    // val classSymbol = TypeRepr.of[V[Column]].classSymbol.get
    // val constructor = classSymbol.primaryConstructor
    // val constructorTypeParameters = constructor.paramSymss(0)
    // val constructorParameters = constructor.paramSymss(1)

    // {
    //   val ownerType = TypeTree.of[V[Column]]
    //   val ownerTypeArgs = ownerType.tpe.typeArgs
    //   println(ownerTypeArgs)
    //   println()
    //   val baseConstructorTerm = Select(New(ownerType), constructor)
    //   val typeAppliedConstructorTerm = TypeApply(baseConstructorTerm, ownerTypeArgs.map(t => TypeTree.ref(t.typeSymbol)))
    //   println(typeAppliedConstructorTerm)
    //   println()
    // }

    {
      val ownerType = TypeTree.of[V[Sc]]
      val ownerTpe = ownerType.tpe
      val ownerTypeArgs = ownerTpe.typeArgs
      println(ownerTypeArgs)
      val constructor = ownerType.tpe.classSymbol.get.primaryConstructor

      val baseCtorTerm = Select(New(ownerType), constructor)
      val typeAppliedCtorTerm = TypeApply(baseCtorTerm, ownerTypeArgs.map(t => TypeTree.ref(t.typeSymbol)))
      println(typeAppliedCtorTerm)
      println()
    }

    // def columnParams(tableRef: Expr[TableRef]) =
    //   for param <- constructorParameters yield
    //     val nameExpr = Expr(param.name)
    //     param.typeRef.translucentSuperType match
    //       case AppliedType(_, List(tp)) => tp.asType match
    //         case '[t] =>
    //           Expr.summon[TypeMapper[t]] match
    //             case Some(mappedType) =>
    //               '{ Column[t]($tableRef, Table.columnNameOverride($tableRef.value)($nameExpr))($mappedType) }.asTerm
    //             case None =>
    //               report.errorAndAbort(s"TypeMapper[$tp] not found.", Position.ofMacroExpansion)

    // def constructorCall__(tableRef: Expr[TableRef]) =
    //   val ownerType = TypeTree.of[V[Column]]
    //   val ownerTypeArgs = ownerType.tpe.typeArgs
    //   val baseConstructorTerm = Select(New(ownerType), constructor)
    //   val typeAppliedConstructorTerm = TypeApply(baseConstructorTerm, ownerTypeArgs.map(t => TypeTree.ref(t.typeSymbol)))
    //   Apply(typeAppliedConstructorTerm, columnParams(tableRef)).asExprOf[V[Column]]

    // def constructorCall[T[_] : Type](params: List[Term]) =
    //   val ownerType = TypeTree.of[V[T]]
    //   val ownerTypeArgs = ownerType.tpe.typeArgs
    //   val baseConstructorTerm = Select(New(ownerType), constructor)
    //   val typeAppliedConstructorTerm = TypeApply(baseConstructorTerm, ownerTypeArgs.map(t => TypeTree.ref(t.typeSymbol)))
    //   val res = Apply(typeAppliedConstructorTerm, params).asExprOf[V[T]]
    //   println(res)
    //   res

    // def subParam[T[_] : Type](tp: TypeRef) =
    //   tp.translucentSuperType match
    //     case AppliedType(_, List(t)) =>
    //       t.asType match
    //         case '[t] => TypeRepr.of[T[t]]

    // def queryables =
    //   Expr.ofList(
    //     for param <- constructorParameters yield
    //       val tpe = subParam[Sc](param.typeRef)
    //       val tpe2 = subParam[SqlExpr](param.typeRef)
    //       (tpe.asType, tpe2.asType) match
    //         case ('[t1], '[t2]) => Expr.summon[Row[t2, t1]].get
    //   )

    // val labels = Expr(constructorParameters.map(_.name))

    // def flattenExprs(queryable: Expr[Metadata.QueryableProxy], table: Expr[V[SqlExpr]]) =
    //   val exprs = 
    //     for (param, i) <- constructorParameters.zipWithIndex yield
    //       val iExpr = Expr(i)
    //       val tpe = subParam[Sc](param.typeRef)
    //       val tpe2 = subParam[SqlExpr](param.typeRef)
    //       (tpe.asType, tpe2.asType) match
    //         case ('[t1], '[t2]) =>
    //           val q = Select(table.asTerm, classSymbol.fieldMember(param.name)).asExprOf[t2]
    //           '{ $queryable.apply[t2, t1]($iExpr).walkExprs($q) }
    //   exprs.reduceLeft: (l, r) =>
    //     '{ $l ++ $r }

    // def construct(queryable: Expr[Metadata.QueryableProxy], args: Expr[ResultSetIterator]) =
    //   val ownerType = TypeTree.of[V[Sc]]
    //   val ownerTypeArgs = ownerType.tpe.typeArgs
    //   val constructor = ownerType.tpe.classSymbol.get.primaryConstructor
    //   // val constructorTypeParameters = constructor.paramSymss(0)
    //   // val constructorParameters = constructor.paramSymss(1)

    //   // val params = for (param, i) <- constructorParameters.zipWithIndex yield
    //   //   val iExpr = Expr(i)
    //   //   val tpe = subParam[Sc](param.typeRef)
    //   //   val tpe2 = subParam[SqlExpr](param.typeRef)
    //   //   (tpe.asType, tpe2.asType) match
    //   //     case ('[t1], '[t2]) =>
    //   //       '{ $queryable.apply[t2, t1]($iExpr).construct($args) : Sc[t1] }.asTerm
    //   val params = List.empty
      
    //   val baseConstructorTerm = Select(New(ownerType), constructor)
    //   val typeAppliedConstructorTerm = TypeApply(baseConstructorTerm, ownerTypeArgs.map(t => TypeTree.ref(t.typeSymbol)))
    //   val res = Apply(typeAppliedConstructorTerm, params).asExprOf[V[Sc]]

    //   println(res.asTerm)
    //   res

    // val queryablesExpr = '{
    //   (dialect: DialectTypeMappers, i: Int) =>
    //     import dialect.given
    //     $queryables(i)
    // }

    // val walkLabelsExpr = '{ () => $labels }

    // val queryableExpr = '{
    //   (walkLabels0: () => Seq[String], dialect: DialectTypeMappers, queryable: Metadata.QueryableProxy) =>
    //     import dialect.given
    //     Table.Internal.TableQueryable[V[SqlExpr], V[Sc]](
    //       walkLabels0,
    //       walkExprs0 = (table: V[SqlExpr]) => ${ flattenExprs('queryable, 'table) },
    //       construct0 = (args: ResultSetIterator) => ${ construct('queryable, 'args) },
    //       deconstruct0 = ???
    //     )
    // }

    // val vExpr0 = '{
    //   (tableRef: TableRef, dialect: DialectTypeMappers, queryable: Metadata.QueryableProxy) =>
    //     import dialect.given
    //     ${ constructorCall__('tableRef) }
    // }

    // '{ Metadata($queryablesExpr, $walkLabelsExpr, $queryableExpr, $vExpr0) }
    '{ ??? }


trait TableMacros:
  inline given metadata[V[_[_]]]: Table.Metadata[V] = ${ TableMacros.metadataImpl[V] }
