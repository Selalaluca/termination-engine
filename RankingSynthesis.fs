namespace TerminationEngine

module RankingSynthesis =
    let private coefficientDomain = [| -1I; 0I; 1I |]
    let private maximumRankingArity = 6

    let rec private enumerateCoefficientVectors arity =
        if arity = 0 then
            seq { yield [||] }
        else
            seq {
                for prefix in enumerateCoefficientVectors (arity - 1) do
                    for coefficient in coefficientDomain do
                        yield Array.append prefix [| coefficient |]
            }

    let private supportSize coefficients =
        coefficients
        |> Array.sumBy (fun coefficient -> if coefficient = 0I then 0 else 1)

    let private coefficientWeight coefficients =
        coefficients |> Array.sumBy abs

    /// 一般線形ランキング用の小さい係数ベクトルを、単純な候補から順に列挙する。
    /// arity制限は候補数の指数的増加を抑えるためで、超過時は安全側に候補なしとする。
    let generateCoefficientVectors arity =
        if arity <= 0 || arity > maximumRankingArity then
            Seq.empty
        else
            enumerateCoefficientVectors arity
            |> Seq.filter (Array.exists ((<>) 0I))
            |> Seq.mapi (fun order coefficients -> order, coefficients)
            |> Seq.sortBy (fun (order, coefficients) ->
                coefficientWeight coefficients,
                supportSize coefficients,
                order)
            |> Seq.map snd

    let private tryRequiredOffset index sign (internalEdges: Edge array) =
        internalEdges
        |> Array.map (fun edge ->
            if index >= edge.Rule.Source.Arguments.Length then None
            else
                match edge.Rule.Source.Arguments[index] with
                | Variable sourceVariable ->
                    RankingVerification.tryGuardLowerBound sourceVariable sign edge.Rule.Guard
                | _ -> None)
        |> Array.fold (fun result bound ->
            match result, bound with
            | Some current, Some lowerBound -> Some(max current (max 0I (-lowerBound)))
            | _ -> None) (Some 0I)

    /// 一般線形候補の係数部分について全内部辺で非負性に必要な定数項を合成する。
    let tryRequiredConstant (coefficients: bigint array) (internalEdges: Edge array) =
        let coefficientOnlyRanking: LinearRanking =
            { Constant = 0I
              Coefficients = Array.copy coefficients }
        internalEdges
        |> Array.map (fun edge ->
            edge.Rule.Source.Arguments
            |> LinearArithmetic.tryInstantiate coefficientOnlyRanking
            |> Option.bind (fun sourceForm ->
                RankingVerification.tryLinearGuardLowerBound sourceForm edge.Rule.Guard))
        |> Array.fold (fun result bound ->
            match result, bound with
            | Some current, Some lowerBound -> Some(max current (max 0I (-lowerBound)))
            | _ -> None) (Some 0I)

    /// 全内部辺で非負かつ厳密減少するxi+cまたは-xi+cを探す。
    /// 発見失敗は非停止の証拠ではなく、現在の候補集合では証明できないことだけを意味する。
    let tryFindProjection (internalEdges: Edge array) =
        // 最初の辺からarityを取得できるか判定し、各引数について正負の射影候補を列挙する。
        match Array.tryHead internalEdges with
        | None -> None
        | Some first ->
            let arity = first.Rule.Source.Arguments.Length
            [ for index in 0 .. first.Rule.Source.Arguments.Length - 1 do
                  for sign in [ 1I; -1I ] do
                      match tryRequiredOffset index sign internalEdges with
                      | Some offset ->
                          let coefficients = Array.zeroCreate arity
                          coefficients[index] <- sign
                          yield ({ Constant = offset; Coefficients = coefficients }: LinearRanking)
                      | None -> () ]
            |> List.tryFind (RankingVerification.verifyProjection internalEdges)

    /// 小さい係数ベクトルを順に具体化し、非負性の定数項と全辺での減少性を満たす候補を探す。
    let tryFindGeneralLinear (internalEdges: Edge array) =
        match Array.tryHead internalEdges with
        | None -> None
        | Some first ->
            first.Rule.Source.Arguments.Length
            |> generateCoefficientVectors
            |> Seq.tryPick (fun coefficients ->
                match tryRequiredConstant coefficients internalEdges with
                | None -> None
                | Some constant ->
                    let candidate: LinearRanking =
                        { Constant = constant
                          Coefficients = Array.copy coefficients }
                    if RankingVerification.verifyLinearDecrease internalEdges candidate then
                        Some candidate
                    else None)

    /// 高速なアフィン射影を先に試し、失敗した場合だけ一般線形候補を探索する。
    let tryFind internalEdges =
        match tryFindProjection internalEdges with
        | Some ranking -> Some ranking
        | None -> tryFindGeneralLinear internalEdges
