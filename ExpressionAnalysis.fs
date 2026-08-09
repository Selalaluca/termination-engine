namespace TerminationEngine

module ExpressionAnalysis =
    /// 任意の整数割当てで式が定義されるかを保守的に判定する。
    /// 除算・剰余は除数が0でないと局所的に分かる場合でも、現在は全域とはみなさない。
    let rec isTotal = function
        | Integer _
        | Variable _ -> true
        | Negate value -> isTotal value
        | Add (left, right)
        | Subtract (left, right)
        | Multiply (left, right) -> isTotal left && isTotal right
        | Divide _
        | Mod _ -> false

    let isUnconditionalTotalRule (rule: Rule) =
        let sourceVariables =
            rule.Source.Arguments
            |> List.choose (function Variable name -> Some name | _ -> None)

        rule.Guard.IsNone
        && sourceVariables.Length = rule.Source.Arguments.Length
        && (sourceVariables |> Set.ofList |> Set.count) = sourceVariables.Length
        && (rule.Target.Arguments |> List.forall isTotal)
