namespace TerminationEngine

open System

module InvariantAnalysis =
    let private conjuncts expression =
        let rec collect result = function
            | And(left, right) -> collect (collect result left) right
            | value -> value :: result
        collect [] expression

    let private tryLocationConstraint (source: Term) atom =
        match atom with
        | Compare(comparison, left, right) ->
            match LinearArithmetic.tryFromExpression left, LinearArithmetic.tryFromExpression right with
            | Some leftForm, Some rightForm ->
                let form = LinearArithmetic.subtract leftForm rightForm
                let positions =
                    source.Arguments
                    |> List.mapi (fun index argument ->
                        match argument with
                        | Variable name -> Some(name, index)
                        | _ -> None)
                    |> List.choose id
                let byName = Map.ofList positions
                if positions.Length <> source.Arguments.Length
                   || byName.Count <> positions.Length
                   || form.Coefficients |> Map.exists (fun name _ -> not (byName.ContainsKey name)) then
                    None
                else
                    let coefficients = Array.zeroCreate source.Arguments.Length
                    for KeyValue(name, coefficient) in form.Coefficients do
                        coefficients[byName[name]] <- coefficient
                    Some {
                        InvariantConstant = form.Constant
                        InvariantCoefficients = coefficients
                        Relation = comparison
                    }
            | _ -> None
        | _ -> None

    /// 線形不変条件を、辺の到着側の状態引数で表現できる場合に伝播する。
    ///
    /// sourceForm = targetForm + delta
    /// となる場合、sourceForm relation 0 は
    /// (targetForm + delta) relation 0 と同値である。例えば
    ///   2*x + y > 0,  (x,y) -> (x+1,y-3)
    /// から、到着側の 2*x+y+1 > 0 を得る。
    /// 係数部分が一致する場合だけを受理するため、逆変換や含意を推測せず健全である。
    let private tryTransferAcrossAffine (edge: Edge) (constraintValue: LinearConstraint) =
        let sourceArguments = edge.Rule.Source.Arguments
        let targetArguments = edge.Rule.Target.Arguments
        if constraintValue.InvariantCoefficients.Length <> sourceArguments.Length
           || sourceArguments.Length <> targetArguments.Length then
            None
        else
            let ranking: LinearRanking =
                { Constant = constraintValue.InvariantConstant
                  Coefficients = Array.copy constraintValue.InvariantCoefficients }
            match
                LinearArithmetic.tryInstantiate ranking sourceArguments,
                LinearArithmetic.tryInstantiate ranking targetArguments
            with
            | Some sourceForm, Some targetForm when sourceForm.Coefficients = targetForm.Coefficients ->
                Some {
                    InvariantConstant = constraintValue.InvariantConstant + sourceForm.Constant - targetForm.Constant
                    InvariantCoefficients = Array.copy constraintValue.InvariantCoefficients
                    Relation = constraintValue.Relation
                }
            | _ -> None

    let private guardConstraints edge =
        edge.Rule.Guard
        |> Option.map conjuncts
        |> Option.defaultValue []
        |> List.choose (tryLocationConstraint edge.Rule.Source)

    let private intersect left right =
        left |> List.filter (fun value -> List.contains value right)

    let private reachableLocations (scc: SccAnalysis) =
        scc.ComponentOf
        |> Array.mapi (fun location componentId -> location, componentId >= 0)
        |> Array.choose (fun (location, reachable) -> if reachable then Some location else None)

    /// ガード付き辺の到着側へ、更新で変化しない線形式の条件を伝播する。
    /// 合流点では全流入辺から得られる共通条件だけを残す。
    let analyse (graph: ControlFlowGraph) (scc: SccAnalysis) : InvariantContext =
        let reachable = reachableLocations scc |> Set.ofArray
        let edges =
            graph.Outgoing
            |> Array.mapi (fun source outgoing ->
                if reachable.Contains source then outgoing else [||])
            |> Array.collect id

        let arityByLocation =
            let arities = Array.create graph.Names.Length None
            for edge in edges do
                if arities[edge.Source].IsNone then
                    arities[edge.Source] <- Some edge.Rule.Source.Arguments.Length
                if arities[edge.Target].IsNone then
                    arities[edge.Target] <- Some edge.Rule.Target.Arguments.Length
            arities

        // ガードから得た制約を単純路に沿って前方伝播し、到着側で使える候補集合を作る。
        // 閉路を同じ位置で再訪する経路は候補生成に使わない。これにより、更新が定数を
        // ずらす閉路でも候補数が無限に増えず、後段の合流点でのmust解析は保守的に保てる。
        let propagatedCandidates = ResizeArray<LinearConstraint>()
        let addCandidate value =
            if not (propagatedCandidates.Contains value) then
                propagatedCandidates.Add value

        let rec propagateFrom location visited constraintValue =
            edges
            |> Array.filter (fun edge -> edge.Source = location)
            |> Array.iter (fun edge ->
                match tryTransferAcrossAffine edge constraintValue with
                | None -> ()
                | Some transferred ->
                    addCandidate transferred
                    if not (Set.contains edge.Target visited) then
                        propagateFrom edge.Target (Set.add edge.Target visited) transferred)

        for edge in edges do
            for constraintValue in guardConstraints edge do
                addCandidate constraintValue
                propagateFrom edge.Source (Set.singleton edge.Source) constraintValue

        let candidatesByArity =
            propagatedCandidates
            |> Seq.groupBy (fun value -> value.InvariantCoefficients.Length)
            |> Seq.map (fun (arity, values) -> arity, values |> Seq.toArray)
            |> Map.ofSeq

        let candidatesFor location =
            arityByLocation[location]
            |> Option.bind (fun arity -> Map.tryFind arity candidatesByArity)
            |> Option.map Array.toList
            |> Option.defaultValue []
            |> List.distinct

        let facts =
            Array.init graph.Names.Length (fun location ->
                if reachable.Contains location && location <> graph.Start then candidatesFor location else [])

        let incoming target = edges |> Array.filter (fun edge -> edge.Target = target)

        let factsFromEdge edge =
            let fromSource =
                facts[edge.Source]
                |> List.choose (tryTransferAcrossAffine edge)
            let fromGuard =
                guardConstraints edge
                |> List.choose (tryTransferAcrossAffine edge)
            (fromSource @ fromGuard) |> List.distinct

        let mutable changed = true
        while changed do
            changed <- false
            for location in reachable do
                if location <> graph.Start then
                    let incomingEdges = incoming location
                    let next =
                        if Array.isEmpty incomingEdges then []
                        else
                            incomingEdges
                            |> Array.map factsFromEdge
                            |> Array.reduce intersect
                    let retained = facts[location] |> List.filter (fun value -> List.contains value next)
                    if retained <> facts[location] then
                        facts[location] <- retained
                        changed <- true

        facts
        |> Array.mapi (fun location values -> location, values)
        |> Array.filter (fun (location, values) -> reachable.Contains location && not (List.isEmpty values))
        |> Map.ofArray
