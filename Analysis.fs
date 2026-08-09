namespace TerminationEngine

type TerminationResult =
    | Yes
    | No of NonTerminationWitness
    | Maybe of CyclicComponent array

module Analysis =
    /// NOの具体的証拠を先に探し、それがなければ全循環SCCの停止証明を試す。
    /// 1成分でも証明できなければ、未証明を停止成功へ近似せずMAYBEを返す。
    let analyse (system: TransitionSystem) =
        let graph = Graph.create system
        let scc = Scc.analyseFromStart graph
        let cyclic = Components.findCyclic graph scc
        let result =
            if cyclic.Length = 0 then Yes
            else
                // まず具体的な非停止証拠の有無を判定し、なければ各SCCのランキング証明へ進む。
                match NonTermination.tryProveObvious graph with
                | Some witness -> No witness
                | None ->
                    if cyclic |> Array.forall (fun cyclicComponent ->
                        cyclicComponent.InternalEdges
                        |> Ranking.tryFindProjection
                        |> Option.isSome) then Yes
                    else Maybe cyclic
        graph, scc, result
