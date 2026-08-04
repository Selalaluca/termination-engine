namespace TerminationEngine

type CyclicComponent = {
    ComponentId: int
    Locations: LocationId array
    InternalEdges: Edge array
    EntryEdges: Edge array
    ExitEdges: Edge array
}

type TerminationResult =
    | Yes
    | No of NonTerminationWitness
    | Maybe of CyclicComponent array

module Analysis =
    let private cyclicComponents (graph: ControlFlowGraph) (scc: SccAnalysis) =
        scc.Components
        |> Array.mapi (fun componentId locations ->
            let members = Set.ofArray locations
            let internalEdges =
                locations
                |> Array.collect (fun location -> graph.Outgoing[location])
                |> Array.filter (fun edge -> members.Contains edge.Target)
            let entryEdges =
                graph.Outgoing
                |> Array.collect id
                |> Array.filter (fun edge ->
                    scc.ComponentOf[edge.Source] >= 0
                    && not (members.Contains edge.Source)
                    && members.Contains edge.Target)
            let exitEdges =
                locations
                |> Array.collect (fun location -> graph.Outgoing[location])
                |> Array.filter (fun edge -> not (members.Contains edge.Target))
            { ComponentId = componentId
              Locations = locations
              InternalEdges = internalEdges
              EntryEdges = entryEdges
              ExitEdges = exitEdges })
        |> Array.filter (fun cyclic ->
            cyclic.Locations.Length > 1
            || cyclic.InternalEdges
               |> Array.exists (fun edge -> edge.Source = edge.Target))

    let analyse (system: TransitionSystem) =
        let graph = Graph.create system
        let scc = Scc.analyseFromStart graph
        let cyclic = cyclicComponents graph scc
        let result =
            if cyclic.Length = 0 then Yes
            else
                match NonTermination.tryProveObvious graph with
                | Some witness -> No witness
                | None -> Maybe cyclic
        graph, scc, result
