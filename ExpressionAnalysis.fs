namespace TerminationEngine

module ExpressionAnalysis =
    /// True when evaluation is defined for every integer valuation.
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
