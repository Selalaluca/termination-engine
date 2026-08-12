namespace TerminationEngine

module Report =
    let renderVerdict result =
        match result with
        | Yes _ -> "YES"
        | No _ -> "NO"
        | Maybe _ -> "MAYBE"

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

    let private renderRanking (proof: RankingProof) =
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

    let private renderRankingMethod = function
        | Projection -> "projection"
        | GeneralLinear -> "general-linear"
        | Z3Linear -> "z3-linear"
        | TransitionRemoval -> "transition-removal"
        | Lexicographic -> "lexicographic"

    let private renderEdges graph edges =
        edges
        |> Array.map (fun edge -> sprintf "%s -> %s" graph.Names[edge.Source] graph.Names[edge.Target])
        |> String.concat ", "

    let private renderLexicographicLevel graph index (level: LexicographicLevel) =
        let method = renderRankingMethod level.Method
        let coefficients = level.Ranking.Coefficients |> Array.map string |> String.concat ", "
        [| sprintf "  level %d method: %s" (index + 1) method
           sprintf "  level %d ranking: constant=%A, coefficients=[%s]" (index + 1) level.Ranking.Constant coefficients
           sprintf "    strict edges: %s" (renderEdges graph level.StrictEdges)
           sprintf "    remaining weak edges: %s" (renderEdges graph level.WeakEdges) |]
    let render (graph: ControlFlowGraph) result =
        // 最終判定を分類し、NOには証拠位置、MAYBEには未解決の循環位置を付加する。
        match result with
        | Yes proofs ->
            let rankings =
                proofs
                |> Array.collect (fun proof ->
                    let componentText = renderComponent graph proof.Component
                    let method = sprintf "%s ranking method: %s" componentText (renderRankingMethod proof.Method)
                    if proof.Method = Lexicographic then
                        Array.concat
                            [ [| method; sprintf "%s lexicographic ranking levels: %d" componentText proof.Levels.Length |]
                              proof.Levels |> Array.mapi (renderLexicographicLevel graph) |> Array.concat
                              [| "  residual graph: acyclic" |] ]
                    else
                        let ranking = sprintf "%s %s" componentText (renderRanking proof)
                        if Array.isEmpty proof.WeakEdges then [| method; ranking |]
                        else
                            [| method
                               ranking
                               sprintf "  strict edges: %s" (renderEdges graph proof.StrictEdges)
                               sprintf "  weak edges: %s" (renderEdges graph proof.WeakEdges)
                               "  weak-only graph: acyclic" |])
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
