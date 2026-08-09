namespace TerminationEngine

/// 数学的整数上のアフィン式。解析器側のオーバーフローを避けるためbigintで保持する。
type LinearForm = {
    Constant: bigint
    Coefficients: Map<string, bigint>
}

module LinearArithmetic =
    let zero = { Constant = 0I; Coefficients = Map.empty }

    let private addCoefficient name amount coefficients =
        let value = amount + (Map.tryFind name coefficients |> Option.defaultValue 0I)
        if value = 0I then Map.remove name coefficients
        else Map.add name value coefficients

    let add left right =
        { Constant = left.Constant + right.Constant
          Coefficients =
            right.Coefficients
            |> Map.fold (fun result name value -> addCoefficient name value result) left.Coefficients }

    let scale factor value =
        { Constant = factor * value.Constant
          Coefficients = value.Coefficients |> Map.map (fun _ coefficient -> factor * coefficient) }

    let subtract left right = add left (scale -1I right)

    let variable name =
        { zero with Coefficients = Map.ofList [ name, 1I ] }

    /// 構文木を厳密にアフィン式へ変換する。変数同士の乗算と部分演算は近似せず拒否する。
    let rec tryFromExpression = function
        | Integer value -> Some { zero with Constant = bigint value }
        | Variable name -> Some(variable name)
        | Negate value -> tryFromExpression value |> Option.map (scale -1I)
        | Add (left, right) ->
            Option.map2 add (tryFromExpression left) (tryFromExpression right)
        | Subtract (left, right) ->
            Option.map2 subtract (tryFromExpression left) (tryFromExpression right)
        | Multiply (Integer factor, value)
        | Multiply (value, Integer factor) ->
            tryFromExpression value |> Option.map (scale (bigint factor))
        | Multiply _
        | Divide _
        | Mod _ -> None
