namespace TerminationEngine

open System.Collections.Concurrent
open System.Numerics
open Microsoft.Z3

module Z3Backend =
    type RankingSample = {
        BeforeArguments: bigint array
        AfterArguments: bigint array
    }

    /// 1回の解析中に同じSMT問い合わせを再利用するためのキー。
    /// Z3のContextやASTは保持せず、入力の値だけをキーにする。
    type private CacheKey = {
        Operation: string
        TimeoutMilliseconds: int
        StrictEdgeIndex: int option
        Invariants: string
        Ranking: string
        Edge: string
        Edges: string
    }

    let private strictRuleCache = ConcurrentDictionary<CacheKey, SmtVerificationResult>()
    let private weakRuleCache = ConcurrentDictionary<CacheKey, SmtVerificationResult>()
    let private sampleCache = ConcurrentDictionary<CacheKey, Result<RankingSample option, string>>()
    let private strictCounterexampleCache =
        ConcurrentDictionary<CacheKey, Result<(int * RankingSample) option, string>>()
    let private removalCounterexampleCache =
        ConcurrentDictionary<CacheKey, Result<(int * RankingSample) option, string>>()

    let private keyText value = sprintf "%A" value

    let private createCacheKey operation timeoutMilliseconds strictEdgeIndex invariants ranking edge edges =
        { Operation = operation
          TimeoutMilliseconds = timeoutMilliseconds
          StrictEdgeIndex = strictEdgeIndex
          Invariants = keyText invariants
          Ranking = keyText ranking
          Edge = keyText edge
          Edges = keyText edges }

    let private getOrAdd
        (cache: ConcurrentDictionary<'key, 'value>)
        (key: 'key)
        (computation: unit -> 'value) =
        match cache.TryGetValue key with
        | true, value -> value
        | false, _ ->
            let value = computation ()
            cache.TryAdd(key, value) |> ignore
            value

    /// 独立した辺に対する問い合わせを並列化する。
    /// 少数の辺ではスレッド切り替えのコストを避ける。
    let private mapInParallel (mapping: 'a -> 'b) (values: 'a array) : 'b array =
        if values.Length < 2 then Array.map mapping values
        else Array.Parallel.map mapping values

    /// 解析開始時に呼び出し、前の解析の結果を持ち越さない。
    let clearCache () =
        strictRuleCache.Clear()
        weakRuleCache.Clear()
        sampleCache.Clear()
        strictCounterexampleCache.Clear()
        removalCounterexampleCache.Clear()

    let private encodeComparison (context: Context) comparison left right =
        match comparison with
        | Eq -> context.MkEq(left, right)
        | NotEq -> context.MkNot(context.MkEq(left, right))
        | Lt -> context.MkLt(left, right)
        | Le -> context.MkLe(left, right)
        | Gt -> context.MkGt(left, right)
        | Ge -> context.MkGe(left, right)

    let private encodeInvariant context environment (constraintValue: LinearConstraint) arguments =
        let ranking: LinearRanking =
            { Constant = constraintValue.InvariantConstant
              Coefficients = Array.copy constraintValue.InvariantCoefficients }
        match LinearArithmetic.tryInstantiate ranking arguments with
        | None -> Error "不変条件を遷移引数へ適用できません。"
        | Some form ->
            let encoded = Z3Encoding.encodeLinearForm environment form
            Ok(encodeComparison context constraintValue.Relation encoded (context.MkInt(0)))

    let private encodeEdgeCondition (context: Context) (environment: Z3Encoding.Environment) (invariants: InvariantContext) (edge: Edge) =
        let guardResult =
            match edge.Rule.Guard with
            | None -> Ok(context.MkTrue())
            | Some value -> Z3Encoding.encodeBool environment value
        let invariantResults =
            invariants
            |> Map.tryFind edge.Source
            |> Option.defaultValue []
            |> List.map (fun constraintValue -> encodeInvariant context environment constraintValue edge.Rule.Source.Arguments)
        match guardResult, invariantResults |> List.tryPick (function Error reason -> Some reason | Ok _ -> None) with
        | Error reason, _ -> Error reason
        | _, Some reason -> Error reason
        | Ok guard, None ->
            let encodedInvariants = invariantResults |> List.choose (function Ok value -> Some value | Error _ -> None)
            Ok(context.MkAnd(Array.append [| guard |] (List.toArray encodedInvariants)))

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

    let private verifyStrictRankingRuleWithInvariantsUncached
        timeoutMilliseconds
        (invariants: InvariantContext)
        (ranking: LinearRanking)
        (edge: Edge) =
        match
            LinearArithmetic.tryInstantiate ranking edge.Rule.Source.Arguments,
            LinearArithmetic.tryInstantiate ranking edge.Rule.Target.Arguments
        with
        | Some before, Some after ->
            use context = new Context()
            let environment = Z3Encoding.createEnvironment context
            let guard = encodeEdgeCondition context environment invariants edge
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

    let verifyStrictRankingRuleWithInvariants timeoutMilliseconds (invariants: InvariantContext) (ranking: LinearRanking) (edge: Edge) =
        let key = createCacheKey "strict-rule" timeoutMilliseconds None invariants ranking edge [||]
        getOrAdd strictRuleCache key (fun () ->
            verifyStrictRankingRuleWithInvariantsUncached timeoutMilliseconds invariants ranking edge)

    let verifyStrictRankingWithInvariants timeoutMilliseconds (invariants: InvariantContext) internalEdges ranking =
        internalEdges
        |> mapInParallel (verifyStrictRankingRuleWithInvariants timeoutMilliseconds invariants ranking)
        |> Array.fold (fun result current ->
            match result, current with
            | Invalid, _
            | _, Invalid -> Invalid
            | Inconclusive reason, _ -> Inconclusive reason
            | _, Inconclusive reason -> Inconclusive reason
            | Valid, Valid -> Valid) Valid

    let verifyStrictRankingRule timeoutMilliseconds ranking edge =
        verifyStrictRankingRuleWithInvariants timeoutMilliseconds Map.empty ranking edge

    let verifyStrictRanking timeoutMilliseconds internalEdges ranking =
        verifyStrictRankingWithInvariants timeoutMilliseconds Map.empty internalEdges ranking

    let private verifyWeakRankingRuleWithInvariantsUncached
        timeoutMilliseconds
        (invariants: InvariantContext)
        (ranking: LinearRanking)
        (edge: Edge) =
        match
            LinearArithmetic.tryInstantiate ranking edge.Rule.Source.Arguments,
            LinearArithmetic.tryInstantiate ranking edge.Rule.Target.Arguments
        with
        | Some before, Some after ->
            use context = new Context()
            let environment = Z3Encoding.createEnvironment context
            let guard = encodeEdgeCondition context environment invariants edge
            match guard with
            | Error reason -> Inconclusive reason
            | Ok encodedGuard ->
                let beforeExpression = Z3Encoding.encodeLinearForm environment before
                let afterExpression = Z3Encoding.encodeLinearForm environment after
                let violation =
                    context.MkAnd(
                        encodedGuard,
                        context.MkOr(
                            context.MkLt(beforeExpression, context.MkInt(0)),
                            context.MkLt(beforeExpression, afterExpression)))
                match check context timeoutMilliseconds violation with
                | Unsat -> Valid
                | Sat -> Invalid
                | Unknown reason -> Inconclusive reason
        | _ -> Inconclusive "ランキング関数を遷移引数へ適用できません。"

    let verifyWeakRankingRuleWithInvariants timeoutMilliseconds (invariants: InvariantContext) (ranking: LinearRanking) (edge: Edge) =
        let key = createCacheKey "weak-rule" timeoutMilliseconds None invariants ranking edge [||]
        getOrAdd weakRuleCache key (fun () ->
            verifyWeakRankingRuleWithInvariantsUncached timeoutMilliseconds invariants ranking edge)

    let verifyWeakRankingRule timeoutMilliseconds ranking edge =
        verifyWeakRankingRuleWithInvariants timeoutMilliseconds Map.empty ranking edge

    let private tryModelInteger (model: Model) (expression: ArithExpr) =
        match model.Evaluate(expression, true) with
        | :? IntNum as value -> Some(BigInteger.Parse(value.ToString()))
        | _ -> None

    /// ガードを満たす具体状態を取り出し、遷移前後の引数値をCEGIS用サンプルにする。
    let private trySampleRuleWithInvariantsUncached timeoutMilliseconds (invariants: InvariantContext) (edge: Edge) =
        use context = new Context()
        let environment = Z3Encoding.createEnvironment context
        let guard = encodeEdgeCondition context environment invariants edge
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

    let trySampleRuleWithInvariants timeoutMilliseconds (invariants: InvariantContext) (edge: Edge) =
        let key = createCacheKey "sample" timeoutMilliseconds None invariants "" edge [||]
        getOrAdd sampleCache key (fun () ->
            trySampleRuleWithInvariantsUncached timeoutMilliseconds invariants edge)

    let trySampleRule timeoutMilliseconds edge =
        trySampleRuleWithInvariants timeoutMilliseconds Map.empty edge

    /// 候補の反例を返す。Noneは全辺で非負性と厳密減少が証明されたことを表す。
    let private tryFindStrictRankingCounterexampleWithInvariantsUncached
        timeoutMilliseconds
        (invariants: InvariantContext)
        (internalEdges: Edge array)
        (ranking: LinearRanking) =
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
                    let guard = encodeEdgeCondition context environment invariants edge
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

    let tryFindStrictRankingCounterexampleWithInvariants
        timeoutMilliseconds
        (invariants: InvariantContext)
        (internalEdges: Edge array)
        (ranking: LinearRanking) =
        let key = createCacheKey "strict-counterexample" timeoutMilliseconds None invariants ranking [||] internalEdges
        getOrAdd strictCounterexampleCache key (fun () ->
            tryFindStrictRankingCounterexampleWithInvariantsUncached timeoutMilliseconds invariants internalEdges ranking)

    let tryFindStrictRankingCounterexample timeoutMilliseconds internalEdges ranking =
        tryFindStrictRankingCounterexampleWithInvariants timeoutMilliseconds Map.empty internalEdges ranking

    /// 全辺の非負・非増加と、指定辺の厳密減少に対する最初の反例を返す。
    let private tryFindRemovalRankingCounterexampleWithInvariantsUncached
        timeoutMilliseconds
        strictEdgeIndex
        (invariants: InvariantContext)
        (internalEdges: Edge array)
        (ranking: LinearRanking) =
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
                    let guard = encodeEdgeCondition context environment invariants edge
                    let sourceArguments = edge.Rule.Source.Arguments |> List.map (Z3Encoding.encodeInt environment)
                    let targetArguments = edge.Rule.Target.Arguments |> List.map (Z3Encoding.encodeInt environment)
                    match guard, sourceArguments |> List.tryPick (function Error error -> Some error | _ -> None), targetArguments |> List.tryPick (function Error error -> Some error | _ -> None) with
                    | Error reason, _, _
                    | _, Some reason, _
                    | _, _, Some reason -> Error reason
                    | Ok encodedGuard, None, None ->
                        let beforeExpression = Z3Encoding.encodeLinearForm environment before
                        let afterExpression = Z3Encoding.encodeLinearForm environment after
                        let requiredDecrease = if index = strictEdgeIndex then context.MkInt(1) else context.MkInt(0)
                        let violation =
                            context.MkOr(
                                context.MkLt(beforeExpression, context.MkInt(0)),
                                context.MkLt(beforeExpression, context.MkAdd(afterExpression, requiredDecrease)))
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

    let tryFindRemovalRankingCounterexampleWithInvariants
        timeoutMilliseconds
        strictEdgeIndex
        (invariants: InvariantContext)
        (internalEdges: Edge array)
        (ranking: LinearRanking) =
        let key = createCacheKey "removal-counterexample" timeoutMilliseconds (Some strictEdgeIndex) invariants ranking [||] internalEdges
        getOrAdd removalCounterexampleCache key (fun () ->
            tryFindRemovalRankingCounterexampleWithInvariantsUncached
                timeoutMilliseconds
                strictEdgeIndex
                invariants
                internalEdges
                ranking)

    let tryFindRemovalRankingCounterexample timeoutMilliseconds strictEdgeIndex internalEdges ranking =
        tryFindRemovalRankingCounterexampleWithInvariants timeoutMilliseconds strictEdgeIndex Map.empty internalEdges ranking
