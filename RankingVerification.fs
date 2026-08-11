namespace TerminationEngine

module RankingVerification =
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

    let verifyProjectionRule candidate (edge: Edge) =
        let rule = edge.Rule
        if candidate.ArgumentIndex >= rule.Source.Arguments.Length
           || candidate.ArgumentIndex >= rule.Target.Arguments.Length then false
        else
            // 対象引数がSourceでは単純変数、Targetではアフィン式として扱えるか判定する。
            match rule.Source.Arguments[candidate.ArgumentIndex] with
            | Variable sourceVariable ->
                // 更新前後の差が定数になり、候補の符号方向へ1以上減るか検査する。
                match LinearArithmetic.tryFromExpression rule.Target.Arguments[candidate.ArgumentIndex] with
                | Some target ->
                    let source = LinearArithmetic.variable sourceVariable
                    let change = LinearArithmetic.subtract target source
                    let decreases =
                        change.Coefficients.IsEmpty
                        && candidate.Sign * change.Constant <= -1I
                    let nonNegative =
                        tryGuardLowerBound sourceVariable candidate.Sign rule.Guard
                        |> Option.exists (fun lowerBound -> lowerBound + candidate.Offset >= 0I)
                    decreases && nonNegative
                | None -> false
            | _ -> false

    let verifyProjection (internalEdges: Edge array) candidate =
        internalEdges |> Array.forall (verifyProjectionRule candidate)
