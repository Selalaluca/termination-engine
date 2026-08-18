namespace TerminationEngine

open System.Numerics
open Microsoft.Z3

module RankingSynthesis =
    type private SynthesisGoal =
        | StrictOnAllEdges
        | WeakOnAllEdgesAndStrictAt of int

    let private coefficientDomain = [| -1I; 0I; 1I |]
    let private maximumRankingArity = 6
    let private z3TimeoutMilliseconds = 1000
    let private cegisIterationLimit = 128

    let private verifyStrictCandidate (invariants: InvariantContext) internalEdges candidate =
        Z3Backend.verifyStrictRankingWithInvariants z3TimeoutMilliseconds invariants internalEdges candidate = Valid

    let private trySynthesizeFromSamples goal arity (samples: Z3Backend.RankingSample list array) : LinearRanking option =
        use context = new Context()
        use solver = context.MkOptimize()
        let parameters = context.MkParams()
        parameters.Add("timeout", uint32 z3TimeoutMilliseconds) |> ignore
        solver.Parameters <- parameters
        let constant = context.MkIntConst("ranking_constant")
        let coefficients = Array.init arity (fun index -> context.MkIntConst($"ranking_c_{index}"))
        coefficients
        |> Array.map (fun coefficient -> context.MkNot(context.MkEq(coefficient, context.MkInt(0))))
        |> context.MkOr
        |> fun constraintExpression -> solver.Add(constraintExpression) |> ignore
        samples
        |> Array.iteri (fun edgeIndex edgeSamples ->
            edgeSamples
            |> List.iter (fun sample ->
                let weighted values =
                    Array.map2 (fun coefficient value ->
                        context.MkMul(coefficient, context.MkInt(string value))) coefficients values
                    |> context.MkAdd
                let before = context.MkAdd(constant, weighted sample.BeforeArguments)
                let decrease = context.MkSub(weighted sample.BeforeArguments, weighted sample.AfterArguments)
                solver.Add(context.MkGe(before, context.MkInt(0))) |> ignore
                let minimumDecrease =
                    match goal with
                    | StrictOnAllEdges -> 1
                    | WeakOnAllEdgesAndStrictAt strictEdgeIndex when edgeIndex = strictEdgeIndex -> 1
                    | WeakOnAllEdgesAndStrictAt _ -> 0
                solver.Add(context.MkGe(decrease, context.MkInt(minimumDecrease))) |> ignore))
        let absolute value =
            context.MkITE(
                context.MkGe(value, context.MkInt(0)),
                value,
                context.MkUnaryMinus(value)) :?> ArithExpr
        coefficients
        |> Array.map absolute
        |> context.MkAdd
        |> solver.MkMinimize
        |> ignore
        absolute constant |> solver.MkMinimize |> ignore
        let goalText =
            match goal with
            | StrictOnAllEdges -> "strict-on-all-edges"
            | WeakOnAllEdgesAndStrictAt index -> sprintf "weak-all-strict-edge-%d" index
        SmtTrace.emit "smt-query" [ "goal", box goalText; "arity", box arity; "sampleCounts", box (samples |> Array.map List.length); "smtLib", box (solver.ToString()) ]
        match solver.Check() with
        | Status.SATISFIABLE ->
            let model = solver.Model
            let read (value: Microsoft.Z3.IntExpr) =
                match model.Evaluate(value, true) with
                | :? IntNum as number -> Some(BigInteger.Parse(number.ToString()))
                | _ -> None
            match read constant, coefficients |> Array.map read |> Array.fold (fun state item -> Option.map2 Array.append state (item |> Option.map Array.singleton)) (Some [||]) with
            | Some constantValue, Some coefficientValues ->
                SmtTrace.emit "smt-result" [ "goal", box goalText; "status", box "sat"; "constant", box (string constantValue); "coefficients", box (coefficientValues |> Array.map string) ]
                Some ({ Constant = constantValue; Coefficients = coefficientValues }: LinearRanking)
            | _ -> SmtTrace.emit "smt-result" [ "goal", box goalText; "status", box "model-read-failed" ]; None
        | Status.UNSATISFIABLE -> SmtTrace.emit "smt-result" [ "goal", box goalText; "status", box "unsat" ]; None
        | Status.UNKNOWN -> SmtTrace.emit "smt-result" [ "goal", box goalText; "status", box "unknown"; "reason", box solver.ReasonUnknown ]; None
        | status -> SmtTrace.emit "smt-result" [ "goal", box goalText; "status", box (sprintf "%A" status) ]; None

    /// 係数を有限集合へ制限せず、Z3と反例検証を往復して一般線形ランキングを合成する。
    let tryFindZ3LinearWithInvariants (invariants: InvariantContext) (internalEdges: Edge array) =
        match Array.tryHead internalEdges with
        | None -> None
        | Some first ->
            let arity = first.Rule.Source.Arguments.Length
            if arity = 0 || internalEdges |> Array.exists (fun edge -> edge.Rule.Source.Arguments.Length <> arity || edge.Rule.Target.Arguments.Length <> arity) then
                None
            else
                let initialSamples =
                    internalEdges
                    |> Array.map (fun edge -> Z3Backend.trySampleRuleWithInvariants z3TimeoutMilliseconds invariants edge)
                if initialSamples |> Array.exists Result.isError then None
                else
                    let samples =
                        initialSamples
                        |> Array.map (function Ok(Some sample) -> [ sample ] | _ -> [])
                    let rec search iteration =
                        SmtTrace.emit "cegis-iteration" [ "goal", box "strict"; "iteration", box iteration; "sampleCounts", box (samples |> Array.map List.length) ]
                        if iteration >= cegisIterationLimit then
                            SmtTrace.emit "cegis-limit" [ "goal", box "strict"; "limit", box cegisIterationLimit ]
                            None
                        else
                            match trySynthesizeFromSamples StrictOnAllEdges arity samples with
                            | None -> SmtTrace.emit "cegis-no-candidate" [ "goal", box "strict"; "iteration", box iteration ]; None
                            | Some candidate ->
                                SmtTrace.emit "cegis-candidate" [ "goal", box "strict"; "iteration", box iteration; "constant", box (string candidate.Constant); "coefficients", box (candidate.Coefficients |> Array.map string) ]
                                match Z3Backend.tryFindStrictRankingCounterexampleWithInvariants z3TimeoutMilliseconds invariants internalEdges candidate with
                                | Ok None -> SmtTrace.emit "cegis-accepted" [ "goal", box "strict"; "iteration", box iteration ]; Some candidate
                                | Ok(Some(edgeIndex, sample)) ->
                                    SmtTrace.emit "cegis-counterexample" [ "goal", box "strict"; "iteration", box iteration; "edgeIndex", box edgeIndex; "before", box (sample.BeforeArguments |> Array.map string); "after", box (sample.AfterArguments |> Array.map string) ]
                                    samples[edgeIndex] <- sample :: samples[edgeIndex]
                                    search (iteration + 1)
                                | Error reason -> SmtTrace.emit "cegis-error" [ "goal", box "strict"; "iteration", box iteration; "reason", box reason ]; None
                    search 0

    /// 全辺で非増加となり、少なくとも指定した1辺で厳密減少する任意整数係数をCEGISで合成する。
    let tryFindZ3RemovalLevelWithInvariants (invariants: InvariantContext) (internalEdges: Edge array) =
        match Array.tryHead internalEdges with
        | None -> None
        | Some first ->
            let arity = first.Rule.Source.Arguments.Length
            if arity = 0 || internalEdges |> Array.exists (fun edge -> edge.Rule.Source.Arguments.Length <> arity || edge.Rule.Target.Arguments.Length <> arity) then
                None
            else
                let initialSamples =
                    internalEdges
                    |> Array.map (Z3Backend.trySampleRuleWithInvariants z3TimeoutMilliseconds invariants)
                if initialSamples |> Array.exists Result.isError then None
                else
                    [ 0 .. internalEdges.Length - 1 ]
                    |> List.tryPick (fun strictEdgeIndex ->
                        match initialSamples[strictEdgeIndex] with
                        | Ok None -> None
                        | Error _ -> None
                        | Ok(Some _) ->
                            let samples =
                                initialSamples
                                |> Array.map (function Ok(Some sample) -> [ sample ] | _ -> [])
                            let rec search iteration =
                                SmtTrace.emit "cegis-iteration" [ "goal", box "removal"; "strictEdgeIndex", box strictEdgeIndex; "iteration", box iteration; "sampleCounts", box (samples |> Array.map List.length) ]
                                if iteration >= cegisIterationLimit then
                                    SmtTrace.emit "cegis-limit" [ "goal", box "removal"; "strictEdgeIndex", box strictEdgeIndex; "limit", box cegisIterationLimit ]
                                    None
                                else
                                    match trySynthesizeFromSamples (WeakOnAllEdgesAndStrictAt strictEdgeIndex) arity samples with
                                    | None -> SmtTrace.emit "cegis-no-candidate" [ "goal", box "removal"; "strictEdgeIndex", box strictEdgeIndex; "iteration", box iteration ]; None
                                    | Some candidate ->
                                        SmtTrace.emit "cegis-candidate" [ "goal", box "removal"; "strictEdgeIndex", box strictEdgeIndex; "iteration", box iteration; "constant", box (string candidate.Constant); "coefficients", box (candidate.Coefficients |> Array.map string) ]
                                        match Z3Backend.tryFindRemovalRankingCounterexampleWithInvariants z3TimeoutMilliseconds strictEdgeIndex invariants internalEdges candidate with
                                        | Error reason -> SmtTrace.emit "cegis-error" [ "goal", box "removal"; "strictEdgeIndex", box strictEdgeIndex; "iteration", box iteration; "reason", box reason ]; None
                                        | Ok(Some(edgeIndex, sample)) ->
                                            SmtTrace.emit "cegis-counterexample" [ "goal", box "removal"; "strictEdgeIndex", box strictEdgeIndex; "iteration", box iteration; "edgeIndex", box edgeIndex; "before", box (sample.BeforeArguments |> Array.map string); "after", box (sample.AfterArguments |> Array.map string) ]
                                            samples[edgeIndex] <- sample :: samples[edgeIndex]
                                            search (iteration + 1)
                                        | Ok None ->
                                            SmtTrace.emit "cegis-accepted" [ "goal", box "removal"; "strictEdgeIndex", box strictEdgeIndex; "iteration", box iteration ]
                                            let classified =
                                                internalEdges
                                                |> Array.map (fun edge ->
                                                    match Z3Backend.verifyStrictRankingRuleWithInvariants z3TimeoutMilliseconds invariants candidate edge with
                                                    | SmtVerificationResult.Valid -> Some(edge, Strict)
                                                    | SmtVerificationResult.Invalid ->
                                                        match Z3Backend.verifyWeakRankingRuleWithInvariants z3TimeoutMilliseconds invariants candidate edge with
                                                        | SmtVerificationResult.Valid -> Some(edge, Weak)
                                                        | _ -> None
                                                    | SmtVerificationResult.Inconclusive _ -> None)
                                            if classified |> Array.exists Option.isNone then None
                                            else
                                                let values = classified |> Array.choose id
                                                let strictEdges = values |> Array.choose (fun (edge, kind) -> if kind = Strict then Some edge else None)
                                                let weakEdges = values |> Array.choose (fun (edge, kind) -> if kind = Weak then Some edge else None)
                                                if Array.isEmpty strictEdges then None
                                                else
                                                    Some {
                                                        Ranking = candidate
                                                        Method = Z3Linear
                                                        StrictEdges = strictEdges
                                                        WeakEdges = weakEdges
                                                    }
                            search 0)

    let tryFindZ3Linear internalEdges =
        tryFindZ3LinearWithInvariants Map.empty internalEdges

    let tryFindZ3RemovalLevel internalEdges =
        tryFindZ3RemovalLevelWithInvariants Map.empty internalEdges

    let rec private enumerateCoefficientVectors arity =
        if arity = 0 then
            seq { yield [||] }
        else
            seq {
                for prefix in enumerateCoefficientVectors (arity - 1) do
                    for coefficient in coefficientDomain do
                        yield Array.append prefix [| coefficient |]
            }

    let private supportSize coefficients =
        coefficients
        |> Array.sumBy (fun coefficient -> if coefficient = 0I then 0 else 1)

    let private coefficientWeight coefficients =
        coefficients |> Array.sumBy abs

    /// 一般線形ランキング用の小さい係数ベクトルを、単純な候補から順に列挙する。
    /// arity制限は候補数の指数的増加を抑えるためで、超過時は安全側に候補なしとする。
    let generateCoefficientVectors arity =
        if arity <= 0 || arity > maximumRankingArity then
            Seq.empty
        else
            enumerateCoefficientVectors arity
            |> Seq.filter (Array.exists ((<>) 0I))
            |> Seq.mapi (fun order coefficients -> order, coefficients)
            |> Seq.sortBy (fun (order, coefficients) ->
                coefficientWeight coefficients,
                supportSize coefficients,
                order)
            |> Seq.map snd

    /// 射影候補はarityに対して線形個しかないため、一般係数列挙のarity上限を超えても探索する。
    let private generateRemovalCoefficientVectors arity =
        let projections =
            seq {
                for index in 0 .. arity - 1 do
                    for sign in [ 1I; -1I ] do
                        let coefficients = Array.zeroCreate arity
                        coefficients[index] <- sign
                        yield coefficients
            }
        let nonProjectionGeneral =
            generateCoefficientVectors arity
            |> Seq.filter (fun coefficients -> supportSize coefficients > 1)
        Seq.append projections nonProjectionGeneral

    let private tryRequiredOffset index sign (internalEdges: Edge array) =
        internalEdges
        |> Array.map (fun edge ->
            if index >= edge.Rule.Source.Arguments.Length then None
            else
                match edge.Rule.Source.Arguments[index] with
                | Variable sourceVariable ->
                    RankingVerification.tryGuardLowerBound sourceVariable sign edge.Rule.Guard
                | _ -> None)
        |> Array.fold (fun result bound ->
            match result, bound with
            | Some current, Some lowerBound -> Some(max current (max 0I (-lowerBound)))
            | _ -> None) (Some 0I)

    /// 一般線形候補の係数部分について全内部辺で非負性に必要な定数項を合成する。
    let tryRequiredConstant (coefficients: bigint array) (internalEdges: Edge array) =
        let coefficientOnlyRanking: LinearRanking =
            { Constant = 0I
              Coefficients = Array.copy coefficients }
        internalEdges
        |> Array.map (fun edge ->
            edge.Rule.Source.Arguments
            |> LinearArithmetic.tryInstantiate coefficientOnlyRanking
            |> Option.bind (fun sourceForm ->
                RankingVerification.tryLinearGuardLowerBound sourceForm edge.Rule.Guard))
        |> Array.fold (fun result bound ->
            match result, bound with
            | Some current, Some lowerBound -> Some(max current (max 0I (-lowerBound)))
            | _ -> None) (Some 0I)

    /// Strict辺の直後にSCC内で実行を継続する辺のガードから、ランキング値の下限を得る。
    /// 無限実行ではStrict辺の後に必ず内部辺を選ぶため、全ての直後内部辺が下限を与える場合は
    /// その最弱下限をStrict辺の実行前にも利用できる。複数段のWeak経路は初期版では扱わない。
    let tryRequiredCycleConstant
        (coefficients: bigint array)
        (strictEdges: Edge array)
        (internalEdges: Edge array) =
        let coefficientOnlyRanking: LinearRanking =
            { Constant = 0I
              Coefficients = Array.copy coefficients }
        strictEdges
        |> Array.map (fun strictEdge ->
            let continuationEdges =
                internalEdges
                |> Array.filter (fun edge -> edge.Source = strictEdge.Target)
            if Array.isEmpty continuationEdges then None
            else
                let bounds =
                    continuationEdges
                    |> Array.map (fun continuation ->
                    continuation.Rule.Source.Arguments
                    |> LinearArithmetic.tryInstantiate coefficientOnlyRanking
                    |> Option.bind (fun sourceForm ->
                        RankingVerification.tryLinearGuardLowerBound sourceForm continuation.Rule.Guard))
                if bounds |> Array.exists Option.isNone then None
                else bounds |> Array.choose id |> Array.min |> Some)
        |> Array.fold (fun result bound ->
            match result, bound with
            | Some current, Some lowerBound -> Some(max current (max 0I (-lowerBound)))
            | _ -> None) (Some 0I)

    /// 全内部辺で非負かつ厳密減少するxi+cまたは-xi+cを探す。
    /// 発見失敗は非停止の証拠ではなく、現在の候補集合では証明できないことだけを意味する。
    let tryFindProjectionWithInvariants (invariants: InvariantContext) (internalEdges: Edge array) =
        // 最初の辺からarityを取得できるか判定し、各引数について正負の射影候補を列挙する。
        match Array.tryHead internalEdges with
        | None -> None
        | Some first ->
            let arity = first.Rule.Source.Arguments.Length
            [ for index in 0 .. first.Rule.Source.Arguments.Length - 1 do
                  for sign in [ 1I; -1I ] do
                      match tryRequiredOffset index sign internalEdges with
                      | Some offset ->
                          let coefficients = Array.zeroCreate arity
                          coefficients[index] <- sign
                          yield ({ Constant = offset; Coefficients = coefficients }: LinearRanking)
                      | None -> () ]
            |> List.tryFind (fun candidate ->
                RankingVerification.verifyProjection internalEdges candidate
                && Z3Backend.verifyStrictRankingWithInvariants z3TimeoutMilliseconds invariants internalEdges candidate = Valid)

    let tryFindProjection internalEdges =
        tryFindProjectionWithInvariants Map.empty internalEdges

    /// 小さい係数ベクトルを順に具体化し、非負性の定数項と全辺での減少性を満たす候補を探す。
    let tryFindGeneralLinearWithInvariants (invariants: InvariantContext) (internalEdges: Edge array) =
        match Array.tryHead internalEdges with
        | None -> None
        | Some first ->
            first.Rule.Source.Arguments.Length
            |> generateCoefficientVectors
            |> Seq.tryPick (fun coefficients ->
                match tryRequiredConstant coefficients internalEdges with
                | None -> None
                | Some constant ->
                    let candidate: LinearRanking =
                        { Constant = constant
                          Coefficients = Array.copy coefficients }
                    if verifyStrictCandidate invariants internalEdges candidate then
                        Some candidate
                    else None)

    let tryFindGeneralLinear internalEdges =
        tryFindGeneralLinearWithInvariants Map.empty internalEdges

    /// 全辺非増加かつWeak辺だけでは循環できない一般線形候補を探す。
    /// 非負性の定数項を全内部辺のガードから合成できる候補だけを対象にする。
    let tryFindTransitionRemoval (internalEdges: Edge array) =
        match Array.tryHead internalEdges with
        | None -> None
        | Some first ->
            first.Rule.Source.Arguments.Length
            |> generateRemovalCoefficientVectors
            |> Seq.tryPick (fun coefficients ->
                let coefficientOnlyCandidate: LinearRanking =
                    { Constant = 0I
                      Coefficients = Array.copy coefficients }
                match RankingVerification.verifyTransitionRemoval internalEdges coefficientOnlyCandidate with
                | None -> None
                | Some(strictEdges, weakEdges) ->
                    let requiredConstant =
                        match tryRequiredConstant coefficients internalEdges with
                        | Some constant -> Some constant
                        | None -> tryRequiredCycleConstant coefficients strictEdges internalEdges
                    requiredConstant
                    |> Option.map (fun constant ->
                        let candidate: LinearRanking =
                            { Constant = constant
                              Coefficients = Array.copy coefficients }
                        candidate, strictEdges, weakEdges))

    let private tryFindRemovalLevel (internalEdges: Edge array) =
        match Array.tryHead internalEdges with
        | None -> None
        | Some first ->
            first.Rule.Source.Arguments.Length
            |> generateRemovalCoefficientVectors
            |> Seq.tryPick (fun coefficients ->
                let coefficientOnlyCandidate: LinearRanking =
                    { Constant = 0I
                      Coefficients = Array.copy coefficients }
                let classified =
                    internalEdges
                    |> Array.map (fun edge ->
                        edge, RankingVerification.classifyLinearDecreaseRule coefficientOnlyCandidate edge)
                if classified |> Array.exists (snd >> (=) Invalid) then None
                else
                    let strictEdges =
                        classified
                        |> Array.choose (fun (edge, kind) -> if kind = Strict then Some edge else None)
                    let weakEdges =
                        classified
                        |> Array.choose (fun (edge, kind) -> if kind = Weak then Some edge else None)
                    if Array.isEmpty strictEdges then None
                    else
                        let requiredConstant =
                            match tryRequiredConstant coefficients internalEdges with
                            | Some constant -> Some constant
                            | None -> tryRequiredCycleConstant coefficients strictEdges internalEdges
                        requiredConstant
                        |> Option.map (fun constant ->
                            let candidate: LinearRanking =
                                { Constant = constant
                                  Coefficients = Array.copy coefficients }
                            let method =
                                if supportSize coefficients = 1 && coefficientWeight coefficients = 1I then Projection
                                else GeneralLinear
                            { Ranking = candidate
                              Method = method
                              StrictEdges = strictEdges
                              WeakEdges = weakEdges }))

    /// Strict辺を段階的に除去し、残余の循環コアを次成分で順位付けする。
    let tryFindLexicographicWithInvariants (invariants: InvariantContext) (internalEdges: Edge array) =
        let maximumDepth = 8
        let rec search depth levels remaining =
            let cyclic = RankingVerification.cyclicEdges remaining
            if Array.isEmpty cyclic then Some(levels |> List.rev |> List.toArray)
            elif depth >= maximumDepth then None
            else
                match tryFindRemovalLevel cyclic with
                | None ->
                    match tryFindZ3RemovalLevelWithInvariants invariants cyclic with
                    | None -> None
                    | Some level ->
                        let next = RankingVerification.cyclicEdges level.WeakEdges
                        if next.Length >= cyclic.Length then None
                        else search (depth + 1) (level :: levels) next
                | Some level ->
                    let next = RankingVerification.cyclicEdges level.WeakEdges
                    if next.Length >= cyclic.Length then None
                    else search (depth + 1) (level :: levels) next
        search 0 [] internalEdges

    let tryFindLexicographic internalEdges =
        tryFindLexicographicWithInvariants Map.empty internalEdges

    let tryFindWithEvidenceAndInvariants (invariants: InvariantContext) internalEdges =
        match tryFindProjectionWithInvariants invariants internalEdges with
        | Some ranking -> Some(ranking, Projection, internalEdges, [||])
        | None ->
            match tryFindGeneralLinearWithInvariants invariants internalEdges with
            | Some ranking -> Some(ranking, GeneralLinear, internalEdges, [||])
            | None ->
                match tryFindZ3LinearWithInvariants invariants internalEdges with
                | Some ranking -> Some(ranking, Z3Linear, internalEdges, [||])
                | None ->
                    tryFindTransitionRemoval internalEdges
                    |> Option.map (fun (ranking, strictEdges, weakEdges) ->
                        ranking, TransitionRemoval, strictEdges, weakEdges)

    let tryFindWithEvidence internalEdges =
        tryFindWithEvidenceAndInvariants Map.empty internalEdges

    /// 高速なアフィン射影を先に試し、失敗した場合だけ一般線形候補を探索する。
    let tryFind internalEdges =
        tryFindWithEvidence internalEdges
        |> Option.map (fun (ranking, _, _, _) -> ranking)
