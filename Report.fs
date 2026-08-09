namespace TerminationEngine

module Report =
    let render (graph: ControlFlowGraph) result =
        // 最終判定を分類し、NOには証拠位置、MAYBEには未解決の循環位置を付加する。
        match result with
        | Yes -> "YES"
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
