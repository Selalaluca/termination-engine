namespace TerminationEngine

open System.Collections.Generic

type NonTerminationWitness = {
    Stem: Edge array
    Loop: Edge
    Reason: string
}

module NonTermination =
    /// Finds an unguarded, everywhere-defined path to an equally safe self-loop.
    let tryProveObvious (graph: ControlFlowGraph) =
        let visited = Array.create graph.Names.Length false
        let predecessor: Edge option array = Array.create graph.Names.Length None
        let queue = Queue<LocationId>()
        visited[graph.Start] <- true
        queue.Enqueue graph.Start

        let safeEdges location =
            graph.Outgoing[location]
            |> Array.filter (fun edge -> ExpressionAnalysis.isUnconditionalTotalRule edge.Rule)

        while queue.Count > 0 do
            let location = queue.Dequeue()
            for edge in safeEdges location do
                if not visited[edge.Target] then
                    visited[edge.Target] <- true
                    predecessor[edge.Target] <- Some edge
                    queue.Enqueue edge.Target

        let loop =
            [| 0 .. graph.Names.Length - 1 |]
            |> Array.tryPick (fun location ->
                if visited[location] then
                    safeEdges location
                    |> Array.tryFind (fun edge -> edge.Target = location)
                else None)

        loop
        |> Option.map (fun loopEdge ->
            let stem = ResizeArray<Edge>()
            let mutable location = loopEdge.Source
            while location <> graph.Start do
                match predecessor[location] with
                | Some edge ->
                    stem.Add edge
                    location <- edge.Source
                | None -> failwith "非停止証拠の到達経路を復元できません。"
            let stemForward = stem.ToArray() |> Array.rev
            { Stem = stemForward
              Loop = loopEdge
              Reason = "ガードがなく、すべての整数状態で定義される自己ループを無限に反復できます。" })
