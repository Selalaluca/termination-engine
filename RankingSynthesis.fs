namespace TerminationEngine

module RankingSynthesis =
    /// 全内部辺で非負かつ厳密減少するxiまたは-xiを探す。
    /// 発見失敗は非停止の証拠ではなく、現在の候補集合では証明できないことだけを意味する。
    let tryFindProjection (internalEdges: Edge array) =
        // 最初の辺からarityを取得できるか判定し、各引数について正負の射影候補を列挙する。
        match Array.tryHead internalEdges with
        | None -> None
        | Some first ->
            [ for index in 0 .. first.Rule.Source.Arguments.Length - 1 do
                  yield { ArgumentIndex = index; Sign = 1I }
                  yield { ArgumentIndex = index; Sign = -1I } ]
            |> List.tryFind (RankingVerification.verifyProjection internalEdges)
