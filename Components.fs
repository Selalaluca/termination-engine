namespace TerminationEngine

type CyclicComponent = {
    ComponentId: int
    Locations: LocationId array
    InternalEdges: Edge array
    EntryEdges: Edge array
    ExitEdges: Edge array
}

module Components =
    /// SCCごとに内部辺・入口辺・出口辺を分類し、実際に閉路を持つ成分だけを返す。
    /// 単一頂点SCCは自己ループがある場合に限って循環成分として扱う。
    let findCyclic (graph: ControlFlowGraph) (scc: SccAnalysis) =
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
