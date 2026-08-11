namespace TerminationEngine

open System.Collections.Generic

type EdgeDecrease =
    | Strict
    | Weak
    | Invalid

module RankingVerification =
    let private tryProjectionShape (candidate: LinearRanking) =
        candidate.Coefficients
        |> Array.indexed
        |> Array.filter (fun (_, coefficient) -> coefficient <> 0I)
        |> function
            | [| index, sign |] when sign = 1I || sign = -1I -> Some(index, sign)
            | _ -> None

    let private conjuncts expression =
        let rec collect result = function
            | And (left, right) -> collect (collect result left) right
            | value -> value :: result
        collect [] expression

    /// 1個の比較から sign * variable の下限を取り出す。
    /// Gt/Ltでは変数が整数であることを使い、厳密境界を1だけずらす。
    let private atomLowerBound variable sign = function
        | Compare (comparison, left, right) ->
            // 比較の両辺を線形式へ変換できるか判定し、left-rightの係数と定数を調べる。
            match LinearArithmetic.tryFromExpression left, LinearArithmetic.tryFromExpression right with
            | Some leftForm, Some rightForm ->
                let difference = LinearArithmetic.subtract leftForm rightForm
                // 差が対象変数1個だけなら、その係数の向きから下限を導ける比較か判定する。
                match Map.toList difference.Coefficients with
                | [ name, coefficient ] when name = variable && coefficient = sign ->
                    match comparison with
                    | Ge -> Some(-difference.Constant)
                    | Gt -> Some(1I - difference.Constant)
                    | Eq -> Some(-difference.Constant)
                    | _ -> None
                | [ name, coefficient ] when name = variable && coefficient = -sign ->
                    // 係数が逆向きの場合は、上限制約をsign*xの下限制約として読み替える。
                    match comparison with
                    | Le -> Some difference.Constant
                    | Lt -> Some(difference.Constant + 1I)
                    | Eq -> Some difference.Constant
                    | _ -> None
                | _ -> None
            | _ -> None
        | _ -> None

    let tryGuardLowerBound variable sign = function
        | None -> None
        | Some guard ->
            guard
            |> conjuncts
            |> List.choose (atomLowerBound variable sign)
            |> function
                | [] -> None
                | bounds -> Some(List.max bounds)

    /// 1個の比較から、指定した一般線形式の下限を取り出す。
    /// 比較式と対象式の係数が同じか符号反転で一致する場合だけ、定数項を移項して扱う。
    let private atomLinearLowerBound (target: LinearForm) = function
        | Compare (comparison, left, right) ->
            match LinearArithmetic.tryFromExpression left, LinearArithmetic.tryFromExpression right with
            | Some leftForm, Some rightForm ->
                let difference = LinearArithmetic.subtract leftForm rightForm
                if difference.Coefficients = target.Coefficients then
                    let constantDelta = difference.Constant - target.Constant
                    match comparison with
                    | Ge -> Some(-constantDelta)
                    | Gt -> Some(1I - constantDelta)
                    | Eq -> Some(-constantDelta)
                    | _ -> None
                elif difference.Coefficients = (target.Coefficients |> Map.map (fun _ value -> -value)) then
                    let constantDelta = difference.Constant + target.Constant
                    match comparison with
                    | Le -> Some constantDelta
                    | Lt -> Some(constantDelta + 1I)
                    | Eq -> Some constantDelta
                    | _ -> None
                else None
            | _ -> None
        | _ -> None

    let tryLinearGuardLowerBound target = function
        | None -> None
        | Some guard ->
            guard
            |> conjuncts
            |> List.choose (atomLinearLowerBound target)
            |> function
                | [] -> None
                | bounds -> Some(List.max bounds)

    let verifyProjectionRule candidate (edge: Edge) =
        let rule = edge.Rule
        match tryProjectionShape candidate with
        | Some(argumentIndex, sign)
            when argumentIndex < rule.Source.Arguments.Length
                 && argumentIndex < rule.Target.Arguments.Length ->
            // 対象引数がSourceでは単純変数、Targetではアフィン式として扱えるか判定する。
            match rule.Source.Arguments[argumentIndex] with
            | Variable sourceVariable ->
                // 更新前後の差が定数になり、候補の符号方向へ1以上減るか検査する。
                match LinearArithmetic.tryFromExpression rule.Target.Arguments[argumentIndex] with
                | Some target ->
                    let source = LinearArithmetic.variable sourceVariable
                    let change = LinearArithmetic.subtract target source
                    let decreases =
                        change.Coefficients.IsEmpty
                        && sign * change.Constant <= -1I
                    let nonNegative =
                        tryGuardLowerBound sourceVariable sign rule.Guard
                        |> Option.exists (fun lowerBound -> lowerBound + candidate.Constant >= 0I)
                    decreases && nonNegative
                | None -> false
            | _ -> false
        | _ -> false

    let verifyProjection (internalEdges: Edge array) candidate =
        internalEdges |> Array.forall (verifyProjectionRule candidate)

    /// 一般線形ランキングを遷移前後の引数へ適用し、ランキング値が1以上減るか検査する。
    /// 初期版では差が定数へ簡約できる場合だけ受理し、状態変数が残る条件付き減少は近似しない。
    let verifyLinearDecreaseRule (candidate: LinearRanking) (edge: Edge) =
        match
            LinearArithmetic.tryInstantiate candidate edge.Rule.Source.Arguments,
            LinearArithmetic.tryInstantiate candidate edge.Rule.Target.Arguments
        with
        | Some before, Some after ->
            let decrease = LinearArithmetic.subtract before after
            decrease.Coefficients.IsEmpty && decrease.Constant >= 1I
        | _ -> false

    let verifyLinearDecrease (internalEdges: Edge array) candidate =
        internalEdges
        |> Array.forall (verifyLinearDecreaseRule candidate)

    let classifyLinearDecreaseRule (candidate: LinearRanking) (edge: Edge) =
        match
            LinearArithmetic.tryInstantiate candidate edge.Rule.Source.Arguments,
            LinearArithmetic.tryInstantiate candidate edge.Rule.Target.Arguments
        with
        | Some before, Some after ->
            let decrease = LinearArithmetic.subtract before after
            if not decrease.Coefficients.IsEmpty then Invalid
            elif decrease.Constant >= 1I then Strict
            elif decrease.Constant >= 0I then Weak
            else Invalid
        | _ -> Invalid

    let private isAcyclic (edges: Edge array) =
        let outgoing = Dictionary<LocationId, ResizeArray<LocationId>>()
        for edge in edges do
            match outgoing.TryGetValue edge.Source with
            | true, targets -> targets.Add edge.Target
            | false, _ ->
                let targets = ResizeArray<LocationId>()
                targets.Add edge.Target
                outgoing.Add(edge.Source, targets)
        let colors = Dictionary<LocationId, int>()
        let rec visit location =
            match colors.TryGetValue location with
            | true, 1 -> false
            | true, 2 -> true
            | _ ->
                colors[location] <- 1
                let childrenAreAcyclic =
                    match outgoing.TryGetValue location with
                    | true, targets -> targets |> Seq.forall visit
                    | false, _ -> true
                if childrenAreAcyclic then colors[location] <- 2
                childrenAreAcyclic
        edges
        |> Array.collect (fun edge -> [| edge.Source; edge.Target |])
        |> Array.distinct
        |> Array.forall visit

    /// 全辺が非増加で、Strict辺を除いたWeak辺だけのグラフが非循環か検査する。
    let verifyTransitionRemoval (internalEdges: Edge array) candidate =
        let classified =
            internalEdges
            |> Array.map (fun edge -> edge, classifyLinearDecreaseRule candidate edge)
        if classified |> Array.exists (snd >> (=) Invalid) then None
        else
            let strictEdges = classified |> Array.choose (fun (edge, kind) -> if kind = Strict then Some edge else None)
            let weakEdges = classified |> Array.choose (fun (edge, kind) -> if kind = Weak then Some edge else None)
            if Array.isEmpty strictEdges || not (isAcyclic weakEdges) then None
            else Some(strictEdges, weakEdges)
