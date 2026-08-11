namespace TerminationEngine

module Report =
    let private renderComponent (graph: ControlFlowGraph) (cyclicComponent: CyclicComponent) =
        cyclicComponent.Locations
        |> Array.map (fun id -> graph.Names[id])
        |> String.concat ", "
        |> sprintf "(%s)"

    let private renderComponents graph components =
        components
        |> Array.map (renderComponent graph)
        |> String.concat ", "

    let private rankingVariables (proof: RankingProof) =
        let arguments =
            proof.Component.InternalEdges
            |> Array.tryHead
            |> Option.map _.Rule.Source.Arguments
            |> Option.defaultValue []
        proof.Ranking.Coefficients
        |> Array.mapi (fun index _ ->
            arguments
            |> List.tryItem index
            |> Option.bind (function Variable name -> Some name | _ -> None)
            |> Option.defaultValue (sprintf "arg%d" index))

    let private renderRanking proof =
        let ranking = proof.Ranking
        let variables = rankingVariables proof
        let variableTerms =
            Array.zip ranking.Coefficients variables
            |> Array.choose (fun (coefficient, variable) ->
                if coefficient = 0I then None
                elif coefficient = 1I then Some variable
                elif coefficient = -1I then Some(sprintf "-%s" variable)
                else Some(sprintf "%A*%s" coefficient variable))
            |> Array.toList
        let terms =
            if ranking.Constant = 0I then variableTerms
            else variableTerms @ [ sprintf "%A" ranking.Constant ]
        let expression =
            match terms with
            | [] -> "0"
            | values -> values |> String.concat " + " |> fun value -> value.Replace("+ -", "- ")
        sprintf
            "ranking: rho(%s) = %s [constant=%A, coefficients=[%s]]"
            (String.concat "," variables)
            expression
            ranking.Constant
            (ranking.Coefficients |> Array.map string |> String.concat ", ")

    let render (graph: ControlFlowGraph) result =
        // 最終判定を分類し、NOには証拠位置、MAYBEには未解決の循環位置を付加する。
        match result with
        | Yes proofs ->
            let rankings =
                proofs
                |> Array.map (fun proof ->
                    sprintf "%s %s" (renderComponent graph proof.Component) (renderRanking proof))
            let details =
                if Array.isEmpty proofs then [||]
                else
                    Array.append
                        [| sprintf "cyclic SCCs: %s" (proofs |> Array.map _.Component |> renderComponents graph) |]
                        rankings
            System.String.Join(System.Environment.NewLine, Array.append [| "YES" |] details)
        | No witness ->
            let rule = witness.Loop.Rule
            let cyclic =
                graph
                |> Scc.analyseFromStart
                |> Components.findCyclic graph
            System.String.Join(
                System.Environment.NewLine,
                [| "NO"
                   sprintf "cyclic SCCs: %s" (renderComponents graph cyclic)
                   sprintf "line %d: %s" rule.Span.Start.Line witness.Reason |])
        | Maybe components ->
            System.String.Join(
                System.Environment.NewLine,
                [| "MAYBE"
                   sprintf "cyclic SCCs: %s" (renderComponents graph components) |])
