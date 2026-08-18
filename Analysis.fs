namespace TerminationEngine

type TerminationResult =
    | Yes of RankingProof array
    | No of NonTerminationWitness
    | Maybe of CyclicComponent array

module Analysis =
    /// NOの具体的証拠を先に探し、それがなければ全循環SCCの停止証明を試す。
    /// 1成分でも証明できなければ、未証明を停止成功へ近似せずMAYBEを返す。
    let analyse (system: TransitionSystem) =
        let graph = Graph.create system
        let scc = Scc.analyseFromStart graph
        let cyclic = Components.findCyclic graph scc
        let invariants = InvariantAnalysis.analyse graph scc
        let result =
            if cyclic.Length = 0 then Yes [||]
            else
                // まず具体的な非停止証拠の有無を判定し、なければ各SCCのランキング証明へ進む。
                match NonTermination.tryProveObvious graph with
                | Some witness -> No witness
                | None ->
                    let proofs =
                        cyclic
                        |> Array.map (fun cyclicComponent ->
                            match Ranking.tryFindWithEvidenceAndInvariants invariants cyclicComponent.InternalEdges with
                            | Some(ranking, method, strictEdges, weakEdges) ->
                                Some {
                                    Component = cyclicComponent
                                    Ranking = ranking
                                    Method = method
                                    StrictEdges = strictEdges
                                    WeakEdges = weakEdges
                                    Levels = [||]
                                }
                            | None ->
                                Ranking.tryFindLexicographicWithInvariants invariants cyclicComponent.InternalEdges
                                |> Option.bind (fun levels ->
                                    if levels.Length < 2 then None
                                    else
                                        let first = levels[0]
                                        Some {
                                            Component = cyclicComponent
                                            Ranking = first.Ranking
                                            Method = Lexicographic
                                            StrictEdges = first.StrictEdges
                                            WeakEdges = first.WeakEdges
                                            Levels = levels
                                        }))
                    if proofs |> Array.forall Option.isSome then
                        proofs |> Array.choose id |> Yes
                    else Maybe cyclic
        graph, scc, result
