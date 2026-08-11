namespace TerminationEngine

open Microsoft.Z3

module Z3Backend =
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
