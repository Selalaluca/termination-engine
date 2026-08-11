namespace TerminationEngine

module Report =
    let private rankingVariable (proof: RankingProof) =
        proof.Component.InternalEdges
        |> Array.tryHead
        |> Option.bind (fun edge ->
            edge.Rule.Source.Arguments
            |> List.tryItem proof.Ranking.ArgumentIndex)
        |> Option.bind (function Variable name -> Some name | _ -> None)
        |> Option.defaultValue (sprintf "arg%d" proof.Ranking.ArgumentIndex)

    let private renderRanking proof =
        let ranking = proof.Ranking
        let variable = rankingVariable proof
        let expression =
            match ranking.Sign, ranking.Offset with
            | sign, offset when sign = 1I && offset = 0I -> variable
            | sign, offset when sign = -1I && offset = 0I -> sprintf "-%s" variable
            | sign, offset when sign = 1I -> sprintf "%s + %A" variable offset
            | sign, offset when sign = -1I -> sprintf "%A - %s" offset variable
            | sign, offset -> sprintf "%A*%s + %A" sign variable offset
        sprintf
            "ranking: rho(%s) = %s [argumentIndex=%d, sign=%A, offset=%A]"
            variable expression ranking.ArgumentIndex ranking.Sign ranking.Offset

    let render (graph: ControlFlowGraph) result =
        // 最終判定を分類し、NOには証拠位置、MAYBEには未解決の循環位置を付加する。
        match result with
        | Yes proofs ->
            let details =
                proofs
                |> Array.collect (fun proof ->
                    let locations =
                        proof.Component.Locations
                        |> Array.map (fun id -> graph.Names[id])
                        |> String.concat ", "
                    [| sprintf "cyclic SCC: %s" locations
                       renderRanking proof |])
            System.String.Join(System.Environment.NewLine, Array.append [| "YES" |] details)
        | No witness ->
            let rule = witness.Loop.Rule
            System.String.Join(
                System.Environment.NewLine,
                [| "NO"
                   sprintf "line %d: %s" rule.Span.Start.Line witness.Reason |])
        | Maybe components ->
            let details =
                components
                |> Array.map (fun cyclic ->
                    let locations =
                        cyclic.Locations
                        |> Array.map (fun id -> graph.Names[id])
                        |> String.concat ", "
                    sprintf "cyclic SCC: %s" locations)
            System.String.Join(System.Environment.NewLine, Array.append [| "MAYBE" |] details)
