namespace TerminationEngine

open System.Numerics
open Microsoft.Z3

module Z3Backend =
    type RankingSample = {
        BeforeArguments: bigint array
        AfterArguments: bigint array
    }

    let private check (context: Context) timeoutMilliseconds (constraintExpression: BoolExpr) =
        use solver = context.MkSolver()
        let parameters = context.MkParams()
        parameters.Add("timeout", uint32 timeoutMilliseconds) |> ignore
        solver.Parameters <- parameters
        solver.Add [| constraintExpression |]
        match solver.Check() with
        | Status.SATISFIABLE -> Sat
        | Status.UNSATISFIABLE -> Unsat
        | Status.UNKNOWN -> Unknown solver.ReasonUnknown
        | status -> Unknown(sprintf "予期しないZ3状態: %A" status)

    let verifyStrictRankingRule timeoutMilliseconds (ranking: LinearRanking) (edge: Edge) =
        match
            LinearArithmetic.tryInstantiate ranking edge.Rule.Source.Arguments,
            LinearArithmetic.tryInstantiate ranking edge.Rule.Target.Arguments
        with
        | Some before, Some after ->
            use context = new Context()
            let environment = Z3Encoding.createEnvironment context
            let guard =
                match edge.Rule.Guard with
                | None -> Ok(context.MkTrue())
                | Some value -> Z3Encoding.encodeBool environment value
            match guard with
            | Error reason -> Inconclusive reason
            | Ok encodedGuard ->
                let beforeExpression = Z3Encoding.encodeLinearForm environment before
                let afterExpression = Z3Encoding.encodeLinearForm environment after
                let zero = context.MkInt(0)
                let one = context.MkInt(1)
                let nonNegativeCounterexample =
                    context.MkAnd([| encodedGuard; context.MkLt(beforeExpression, zero) |])
                let decreaseCounterexample =
                    context.MkAnd(
                        [| encodedGuard
                           context.MkLt(beforeExpression, context.MkAdd(afterExpression, one)) |])
                match
                    check context timeoutMilliseconds nonNegativeCounterexample,
                    check context timeoutMilliseconds decreaseCounterexample
                with
                | Unsat, Unsat -> Valid
                | Sat, _
                | _, Sat -> Invalid
                | Unknown reason, _
                | _, Unknown reason -> Inconclusive reason
        | _ -> Inconclusive "ランキング関数を遷移引数へ適用できません。"

    let verifyStrictRanking timeoutMilliseconds internalEdges ranking =
        internalEdges
        |> Array.map (verifyStrictRankingRule timeoutMilliseconds ranking)
        |> Array.fold (fun result current ->
            match result, current with
            | Invalid, _
            | _, Invalid -> Invalid
            | Inconclusive reason, _ -> Inconclusive reason
            | _, Inconclusive reason -> Inconclusive reason
            | Valid, Valid -> Valid) Valid

    let private tryModelInteger (model: Model) (expression: ArithExpr) =
        match model.Evaluate(expression, true) with
        | :? IntNum as value -> Some(BigInteger.Parse(value.ToString()))
        | _ -> None

    /// ガードを満たす具体状態を取り出し、遷移前後の引数値をCEGIS用サンプルにする。
    let trySampleRule timeoutMilliseconds (edge: Edge) =
        use context = new Context()
        let environment = Z3Encoding.createEnvironment context
        let guard =
            match edge.Rule.Guard with
            | None -> Ok(context.MkTrue())
            | Some value -> Z3Encoding.encodeBool environment value
        let before = edge.Rule.Source.Arguments |> List.map (Z3Encoding.encodeInt environment)
        let after = edge.Rule.Target.Arguments |> List.map (Z3Encoding.encodeInt environment)
        match guard, before |> List.tryPick (function Error error -> Some error | _ -> None), after |> List.tryPick (function Error error -> Some error | _ -> None) with
        | Error reason, _, _
        | _, Some reason, _
        | _, _, Some reason -> Error reason
        | Ok encodedGuard, None, None ->
            use solver = context.MkSolver()
            let parameters = context.MkParams()
            parameters.Add("timeout", uint32 timeoutMilliseconds) |> ignore
            solver.Parameters <- parameters
            solver.Add encodedGuard
            match solver.Check() with
            | Status.UNSATISFIABLE -> Ok None
            | Status.UNKNOWN -> Error solver.ReasonUnknown
            | Status.SATISFIABLE ->
                let model = solver.Model
                let read expressions =
                    expressions
                    |> List.choose (function Ok value -> tryModelInteger model value | Error _ -> None)
                    |> List.toArray
                let beforeValues = read before
                let afterValues = read after
                if beforeValues.Length = before.Length && afterValues.Length = after.Length then
                    Ok(Some { BeforeArguments = beforeValues; AfterArguments = afterValues })
                else Error "Z3モデルから遷移引数の整数値を取得できません。"
            | status -> Error(sprintf "予期しないZ3状態: %A" status)

    /// 候補の反例を返す。Noneは全辺で非負性と厳密減少が証明されたことを表す。
    let tryFindStrictRankingCounterexample timeoutMilliseconds (internalEdges: Edge array) (ranking: LinearRanking) =
        let rec inspect index =
            if index >= internalEdges.Length then Ok None
            else
                let edge = internalEdges[index]
                match
                    LinearArithmetic.tryInstantiate ranking edge.Rule.Source.Arguments,
                    LinearArithmetic.tryInstantiate ranking edge.Rule.Target.Arguments
                with
                | Some before, Some after ->
                    use context = new Context()
                    let environment = Z3Encoding.createEnvironment context
                    let guard =
                        match edge.Rule.Guard with
                        | None -> Ok(context.MkTrue())
                        | Some value -> Z3Encoding.encodeBool environment value
                    let sourceArguments = edge.Rule.Source.Arguments |> List.map (Z3Encoding.encodeInt environment)
                    let targetArguments = edge.Rule.Target.Arguments |> List.map (Z3Encoding.encodeInt environment)
                    match guard, sourceArguments |> List.tryPick (function Error error -> Some error | _ -> None), targetArguments |> List.tryPick (function Error error -> Some error | _ -> None) with
                    | Error reason, _, _
                    | _, Some reason, _
                    | _, _, Some reason -> Error reason
                    | Ok encodedGuard, None, None ->
                        let beforeExpression = Z3Encoding.encodeLinearForm environment before
                        let afterExpression = Z3Encoding.encodeLinearForm environment after
                        let violation =
                            context.MkOr(
                                context.MkLt(beforeExpression, context.MkInt(0)),
                                context.MkLt(beforeExpression, context.MkAdd(afterExpression, context.MkInt(1))))
                        use solver = context.MkSolver()
                        let parameters = context.MkParams()
                        parameters.Add("timeout", uint32 timeoutMilliseconds) |> ignore
                        solver.Parameters <- parameters
                        solver.Add(context.MkAnd(encodedGuard, violation))
                        match solver.Check() with
                        | Status.UNSATISFIABLE -> inspect (index + 1)
                        | Status.UNKNOWN -> Error solver.ReasonUnknown
                        | Status.SATISFIABLE ->
                            let model = solver.Model
                            let read expressions =
                                expressions
                                |> List.choose (function Ok value -> tryModelInteger model value | Error _ -> None)
                                |> List.toArray
                            let beforeValues = read sourceArguments
                            let afterValues = read targetArguments
                            if beforeValues.Length = sourceArguments.Length && afterValues.Length = targetArguments.Length then
                                Ok(Some(index, { BeforeArguments = beforeValues; AfterArguments = afterValues }))
                            else Error "Z3反例から遷移引数の整数値を取得できません。"
                        | status -> Error(sprintf "予期しないZ3状態: %A" status)
                | _ -> Error "ランキング関数を遷移引数へ適用できません。"
        inspect 0
