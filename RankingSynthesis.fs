namespace TerminationEngine

module RankingSynthesis =
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

    /// 全内部辺で非負かつ厳密減少するxi+cまたは-xi+cを探す。
    /// 発見失敗は非停止の証拠ではなく、現在の候補集合では証明できないことだけを意味する。
    let tryFindProjection (internalEdges: Edge array) =
        // 最初の辺からarityを取得できるか判定し、各引数について正負の射影候補を列挙する。
        match Array.tryHead internalEdges with
        | None -> None
        | Some first ->
            [ for index in 0 .. first.Rule.Source.Arguments.Length - 1 do
                  for sign in [ 1I; -1I ] do
                      match tryRequiredOffset index sign internalEdges with
                      | Some offset ->
                          yield { ArgumentIndex = index; Sign = sign; Offset = offset }
                      | None -> () ]
            |> List.tryFind (RankingVerification.verifyProjection internalEdges)
