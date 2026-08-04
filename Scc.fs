namespace TerminationEngine

open System.Collections.Generic

type SccAnalysis = {
    Components: LocationId array array
    ComponentOf: int array
}

module Scc =
    let analyseFromStart (graph: ControlFlowGraph) =
        let count = graph.Names.Length
        let indices = Array.create count -1
        let lowLinks = Array.zeroCreate count
        let onStack = Array.create count false
        let stack = Stack<LocationId>()
        let components = ResizeArray<LocationId array>()
        let mutable nextIndex = 0

        let rec strongConnect location =
            indices[location] <- nextIndex
            lowLinks[location] <- nextIndex
            nextIndex <- nextIndex + 1
            stack.Push location
            onStack[location] <- true

            for edge in graph.Outgoing[location] do
                let target = edge.Target
                if indices[target] = -1 then
                    strongConnect target
                    lowLinks[location] <- min lowLinks[location] lowLinks[target]
                elif onStack[target] then
                    lowLinks[location] <- min lowLinks[location] indices[target]

            if lowLinks[location] = indices[location] then
                let sccMembers = ResizeArray<LocationId>()
                let mutable finished = false
                while not finished do
                    let memberLocation = stack.Pop()
                    onStack[memberLocation] <- false
                    sccMembers.Add memberLocation
                    finished <- memberLocation = location
                components.Add(sccMembers.ToArray())

        if count > 0 then strongConnect graph.Start

        let componentOf = Array.create count -1
        components
        |> Seq.iteri (fun componentId sccMembers ->
            for location in sccMembers do
                componentOf[location] <- componentId)

        { Components = components.ToArray(); ComponentOf = componentOf }
