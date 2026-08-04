namespace TerminationEngine

open System.Collections.Generic

type LocationId = int

type Edge = {
    Source: LocationId
    Target: LocationId
    Rule: Rule
}

type ControlFlowGraph = {
    Start: LocationId
    Names: string array
    Outgoing: Edge array array
}

module Graph =
    let create (system: TransitionSystem) =
        let ids = Dictionary<string, LocationId>()
        let names = ResizeArray<string>()

        let locationId name =
            match ids.TryGetValue name with
            | true, id -> id
            | false, _ ->
                let id = names.Count
                ids.Add(name, id)
                names.Add name
                id

        let start = locationId system.Start
        let edges =
            system.Rules
            |> List.map (fun rule ->
                { Source = locationId rule.Source.Symbol
                  Target = locationId rule.Target.Symbol
                  Rule = rule })

        let outgoing = Array.init names.Count (fun _ -> ResizeArray<Edge>())
        for edge in edges do
            outgoing[edge.Source].Add edge

        { Start = start
          Names = names.ToArray()
          Outgoing = outgoing |> Array.map _.ToArray() }
