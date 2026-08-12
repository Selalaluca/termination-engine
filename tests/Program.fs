open System
open System.IO
open TerminationEngine

let require condition message = if not condition then failwith message
let readTestFixture relative = File.ReadAllText(Path.Combine(__SOURCE_DIRECTORY__, "fixtures", relative))
let parseTestFixture relative = readTestFixture relative |> KoatParser.parse

let unitTests = [
    "generated files", fun () ->
        for name in [ "Linear"; "IfElse"; "Switch"; "StackMerge"; "Infinite" ] do
            let parsed = parseTestFixture (Path.Combine("generated", name + ".koat"))
            require (not parsed.Rules.IsEmpty) (name + " has no rules")
    "line comments", fun () ->
        let parsed = parseTestFixture (Path.Combine("parser", "line-comments.koat"))
        require (parsed.Rules.Length = 1) "comment changed parsing"
    "precedence and locations", fun () ->
        let parsed = parseTestFixture (Path.Combine("parser", "precedence-and-locations.koat"))
        require (parsed.Rules.Head.Span.Start.Line = 5) "wrong rule line"
        match parsed.Rules.Head.Target.Arguments.Head with Add(Variable "x", Multiply(Variable "y", Integer 2L)) -> () | _ -> failwith "wrong precedence"
    "division and remainder", fun () ->
        let parsed = parseTestFixture (Path.Combine("parser", "division-and-remainder.koat"))
        match parsed.Rules.Head.Target.Arguments with
        | [ Add(Variable "x", Mod(Divide(Variable "y", Integer 2L), Integer 3L))
            Divide(Multiply(Variable "x", Variable "y"), Integer 4L) ] -> ()
        | _ -> failwith "wrong division/remainder precedence or associativity"
    "undeclared variable", fun () ->
        match readTestFixture (Path.Combine("invalid", "undeclared-variable.koat")) |> KoatParser.tryParse with
        | Error error -> require (error.Message.Contains "未宣言") "wrong error"
        | Ok _ -> failwith "accepted undeclared variable"
    "arity mismatch", fun () ->
        match readTestFixture (Path.Combine("invalid", "arity-mismatch.koat")) |> KoatParser.tryParse with
        | Error error -> require (error.Message.Contains "引数数") "wrong error"
        | Ok _ -> failwith "accepted arity mismatch"
    "syntax location", fun () ->
        match readTestFixture (Path.Combine("invalid", "invalid-arrow.koat")) |> KoatParser.tryParse with
        | Error error -> require (error.Position.Line = 5) "wrong syntax error line"
        | Ok _ -> failwith "accepted invalid arrow"
    "SCC from start ignores unreachable cycle", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "unreachable-cycle.koat"))
        let graph = Graph.create system
        let scc = Scc.analyseFromStart graph
        let dead = graph.Names |> Array.findIndex ((=) "dead")
        require (scc.ComponentOf[dead] = -1) "unreachable cycle was visited"
        let _, _, result = Analysis.analyse system
        match result with Yes proofs -> require (Array.isEmpty proofs) "acyclic result contained ranking proofs" | _ -> failwith "unreachable cycle affected termination"
    "reachable multi-node SCC", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "reachable-multi-node-scc.koat"))
        let graph, scc, result = Analysis.analyse system
        let a = graph.Names |> Array.findIndex ((=) "a")
        let b = graph.Names |> Array.findIndex ((=) "b")
        require (scc.ComponentOf[a] = scc.ComponentOf[b]) "cycle nodes were split"
        match result with
        | Maybe [| cyclic |] -> require (cyclic.Locations.Length = 2) "wrong cyclic component"
        | _ -> failwith "reachable cycle was not MAYBE"
    "reachable self-loop SCC", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "countdown.koat"))
        let _, _, result = Analysis.analyse system
        match result with Yes [| _ |] -> () | _ -> failwith "countdown loop did not have a projection ranking"
    "negative projection ranking", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "countup-to-zero.koat"))
        let _, _, result = Analysis.analyse system
        match result with Yes [| proof |] -> require (proof.Ranking.Coefficients = [| -1I |]) "count-up-to-zero loop did not use -x" | _ -> failwith "count-up-to-zero loop was not proven"
    "affine positive projection ranking", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "affine-positive.koat"))
        let graph = Graph.create system
        let cyclicComponent = Components.findCyclic graph (Scc.analyseFromStart graph) |> Array.exactlyOne
        match Ranking.tryFindProjection cyclicComponent.InternalEdges with
        | Some ranking ->
            require (ranking.Constant = 9I && ranking.Coefficients = [| 1I |]) "wrong affine positive ranking"
        | None -> failwith "x + 9 ranking was not found"
    "affine negative projection ranking", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "affine-negative.koat"))
        let graph = Graph.create system
        let cyclicComponent = Components.findCyclic graph (Scc.analyseFromStart graph) |> Array.exactlyOne
        match Ranking.tryFindProjection cyclicComponent.InternalEdges with
        | Some ranking ->
            require (ranking.Constant = 9I && ranking.Coefficients = [| -1I |]) "wrong affine negative ranking"
        | None -> failwith "9 - x ranking was not found"
    "general linear coefficient enumeration", fun () ->
        let candidates = RankingSynthesis.generateCoefficientVectors 2 |> Seq.toArray
        require (candidates.Length = 8) "wrong number of two-variable coefficient candidates"
        require (candidates |> Array.contains [| 1I; 1I |]) "x+y candidate was not generated"
        require (candidates |> Array.contains [| 1I; -1I |]) "x-y candidate was not generated"
        require (candidates |> Array.contains [| 0I; 0I |] |> not) "zero candidate was generated"
        require
            (candidates
             |> Array.take 4
             |> Array.forall (fun coefficients ->
                 coefficients |> Array.filter ((<>) 0I) |> Array.length = 1))
            "projection candidates were not prioritized"
    "linear coefficient enumeration arity limit", fun () ->
        require
            (RankingSynthesis.generateCoefficientVectors 7 |> Seq.isEmpty)
            "coefficient enumeration exceeded its arity limit"
    "instantiate general linear ranking", fun () ->
        let ranking = { Constant = 3I; Coefficients = [| 1I; 1I |] }
        match LinearArithmetic.tryInstantiate ranking [ Variable "x"; Subtract(Variable "y", Integer 1L) ] with
        | Some form ->
            require (form.Constant = 2I) "wrong instantiated constant"
            require (form.Coefficients = Map [ "x", 1I; "y", 1I ]) "wrong instantiated coefficients"
        | None -> failwith "general linear ranking was not instantiated"
    "instantiate ranking rejects arity mismatch", fun () ->
        let ranking = { Constant = 0I; Coefficients = [| 1I; 1I |] }
        require
            (LinearArithmetic.tryInstantiate ranking [ Variable "x" ] |> Option.isNone)
            "ranking arity mismatch was accepted"
    "zero ranking coefficient ignores unsupported argument", fun () ->
        let ranking = { Constant = 0I; Coefficients = [| 1I; 0I |] }
        match LinearArithmetic.tryInstantiate ranking [ Variable "x"; Multiply(Variable "y", Variable "y") ] with
        | Some form -> require (form = LinearArithmetic.variable "x") "zero coefficient changed ranking form"
        | None -> failwith "zero coefficient inspected an irrelevant nonlinear argument"
    "nonzero ranking coefficient rejects unsupported argument", fun () ->
        let ranking = { Constant = 0I; Coefficients = [| 1I |] }
        require
            (LinearArithmetic.tryInstantiate ranking [ Multiply(Variable "x", Variable "x") ] |> Option.isNone)
            "nonlinear ranked argument was accepted"
    "general linear ranking decreases on every edge", fun () ->
        let system = parseTestFixture (Path.Combine("cases", "test15.koat"))
        let graph = Graph.create system
        let cyclicComponent = Components.findCyclic graph (Scc.analyseFromStart graph) |> Array.exactlyOne
        let ranking = { Constant = 0I; Coefficients = [| 1I; 1I |] }
        require
            (RankingVerification.verifyLinearDecrease cyclicComponent.InternalEdges ranking)
            "x+y did not decrease on every test15 edge"
    "incomplete linear ranking does not decrease on every edge", fun () ->
        let system = parseTestFixture (Path.Combine("cases", "test15.koat"))
        let graph = Graph.create system
        let cyclicComponent = Components.findCyclic graph (Scc.analyseFromStart graph) |> Array.exactlyOne
        let ranking = { Constant = 0I; Coefficients = [| 1I; 0I |] }
        require
            (RankingVerification.verifyLinearDecrease cyclicComponent.InternalEdges ranking |> not)
            "x was accepted although the y-only update does not decrease it"
    "state-dependent decrease is deferred", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "state-dependent-decrease.koat"))
        let graph = Graph.create system
        let cyclicComponent = Components.findCyclic graph (Scc.analyseFromStart graph) |> Array.exactlyOne
        let ranking = { Constant = 0I; Coefficients = [| 1I |] }
        require
            (RankingVerification.verifyLinearDecrease cyclicComponent.InternalEdges ranking |> not)
            "state-dependent decrease was accepted without SMT verification"
    "Z3 validates strict general linear ranking", fun () ->
        let system = parseTestFixture (Path.Combine("cases", "test15.koat"))
        let graph = Graph.create system
        let cyclicComponent = Components.findCyclic graph (Scc.analyseFromStart graph) |> Array.exactlyOne
        let ranking = { Constant = 0I; Coefficients = [| 1I; 1I |] }
        require
            (Z3Backend.verifyStrictRanking 1000 cyclicComponent.InternalEdges ranking = Valid)
            "Z3 did not validate x+y"
    "Z3 finds non-decreasing counterexample", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "non-decreasing.koat"))
        let graph = Graph.create system
        let cyclicComponent = Components.findCyclic graph (Scc.analyseFromStart graph) |> Array.exactlyOne
        let ranking = { Constant = 0I; Coefficients = [| 1I |] }
        require
            (Z3Backend.verifyStrictRanking 1000 cyclicComponent.InternalEdges ranking = Invalid)
            "Z3 missed a non-decreasing counterexample"
    "Z3 proves state-dependent decrease", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "state-dependent-decrease.koat"))
        let graph = Graph.create system
        let cyclicComponent = Components.findCyclic graph (Scc.analyseFromStart graph) |> Array.exactlyOne
        let ranking = { Constant = 0I; Coefficients = [| 1I |] }
        require
            (Z3Backend.verifyStrictRanking 1000 cyclicComponent.InternalEdges ranking = Valid)
            "Z3 did not prove the guard-dependent decrease"
    "Z3 state-dependent proof affects final analysis", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "state-dependent-decrease.koat"))
        let _, _, result = Analysis.analyse system
        match result with
        | Yes [| proof |] -> require (proof.Ranking.Coefficients = [| 1I |]) "Z3 final proof selected the wrong ranking"
        | _ -> failwith "Z3 state-dependent proof did not reach the final analysis"
    "Z3 rejects unsupported nonlinear guard", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "nonlinear-guard.koat"))
        let graph = Graph.create system
        let cyclicComponent = Components.findCyclic graph (Scc.analyseFromStart graph) |> Array.exactlyOne
        let ranking = { Constant = 0I; Coefficients = [| 1I |] }
        match Z3Backend.verifyStrictRanking 1000 cyclicComponent.InternalEdges ranking with
        | Inconclusive _ -> ()
        | _ -> failwith "nonlinear guard was accepted by the linear SMT encoding"
    "general linear ranking constant synthesis", fun () ->
        let system = parseTestFixture (Path.Combine("cases", "test15.koat"))
        let graph = Graph.create system
        let cyclicComponent = Components.findCyclic graph (Scc.analyseFromStart graph) |> Array.exactlyOne
        require
            (RankingSynthesis.tryRequiredConstant [| 1I; 1I |] cyclicComponent.InternalEdges = Some 0I)
            "x+y did not obtain constant zero"
    "shifted general linear ranking constant synthesis", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "shifted-linear.koat"))
        let graph = Graph.create system
        let cyclicComponent = Components.findCyclic graph (Scc.analyseFromStart graph) |> Array.exactlyOne
        require
            (RankingSynthesis.tryRequiredConstant [| 1I; 1I |] cyclicComponent.InternalEdges = Some 9I)
            "x+y+9 constant was not synthesized"
    "general linear constant uses strongest conjunct", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "strongest-conjunct.koat"))
        let graph = Graph.create system
        let cyclicComponent = Components.findCyclic graph (Scc.analyseFromStart graph) |> Array.exactlyOne
        require
            (RankingSynthesis.tryRequiredConstant [| 1I; 1I |] cyclicComponent.InternalEdges = Some 9I)
            "strongest general linear lower bound was not used"
    "unrelated guard cannot bound general linear ranking", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "unrelated-ranking-guard.koat"))
        let graph = Graph.create system
        let cyclicComponent = Components.findCyclic graph (Scc.analyseFromStart graph) |> Array.exactlyOne
        require
            (RankingSynthesis.tryRequiredConstant [| 1I; 1I |] cyclicComponent.InternalEdges |> Option.isNone)
            "x guard was unsafely used as an x+y lower bound"
    "general linear ranking synthesis", fun () ->
        let system = parseTestFixture (Path.Combine("cases", "test15.koat"))
        let graph = Graph.create system
        let cyclicComponent = Components.findCyclic graph (Scc.analyseFromStart graph) |> Array.exactlyOne
        match Ranking.tryFind cyclicComponent.InternalEdges with
        | Some ranking ->
            require (ranking.Constant = 0I) "x+y ranking received the wrong constant"
            require (ranking.Coefficients = [| 1I; 1I |]) "x+y ranking was not selected"
        | None -> failwith "general linear ranking was not synthesized"
    "general linear ranking affects final analysis", fun () ->
        let system = parseTestFixture (Path.Combine("cases", "test15.koat"))
        let graph, _, result = Analysis.analyse system
        match result with
        | Yes [| proof |] ->
            require (proof.Ranking.Coefficients = [| 1I; 1I |]) "final proof did not retain x+y"
            require ((Report.render graph result).Contains("rho(x,y) = x + y")) "report omitted x+y ranking"
        | _ -> failwith "test15 was not proven by its general linear ranking"
    "Z3 synthesizes unrestricted linear coefficients", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "z3-arbitrary-coefficients.koat"))
        let graph = Graph.create system
        let cyclicComponent = Components.findCyclic graph (Scc.analyseFromStart graph) |> Array.exactlyOne
        match Ranking.tryFindZ3Linear cyclicComponent.InternalEdges with
        | Some ranking ->
            require (ranking.Coefficients = [| 3I; 2I |]) "Z3 did not synthesize coefficients [3, 2]"
            require
                (Z3Backend.verifyStrictRanking 1000 cyclicComponent.InternalEdges ranking = Valid)
                "the synthesized ranking failed independent verification"
        | None -> failwith "Z3 did not synthesize an unrestricted linear ranking"
    "Z3 unrestricted coefficients affect final analysis", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "z3-arbitrary-coefficients.koat"))
        let graph, _, result = Analysis.analyse system
        match result with
        | Yes [| proof |] ->
            require (proof.Ranking.Coefficients = [| 3I; 2I |]) "final proof did not retain coefficients [3, 2]"
            require ((Report.render graph result).Contains("3*x + 2*y")) "report omitted the synthesized ranking"
        | _ -> failwith "unrestricted Z3 synthesis did not reach the final analysis"
    "Z3 CEGIS iteration limit boundary", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "z3-arbitrary-coefficients.koat"))
        let graph = Graph.create system
        let internalEdges =
            Components.findCyclic graph (Scc.analyseFromStart graph)
            |> Array.exactlyOne
            |> fun cyclicComponent -> cyclicComponent.InternalEdges
        require
            (Ranking.tryFindZ3LinearWithLimit 0 internalEdges |> Option.isNone)
            "CEGIS ignored a zero iteration limit"
        let minimumSuccessfulLimit =
            [ 1 .. 128 ]
            |> List.tryFind (fun limit -> Ranking.tryFindZ3LinearWithLimit limit internalEdges |> Option.isSome)
        match minimumSuccessfulLimit with
        | None -> failwith "CEGIS did not converge within 128 iterations"
        | Some minimum ->
            if minimum > 1 then
                require
                    (Ranking.tryFindZ3LinearWithLimit (minimum - 1) internalEdges |> Option.isNone)
                    "CEGIS succeeded below its measured iteration boundary"
            require
                (Ranking.tryFindZ3LinearWithLimit minimum internalEdges |> Option.isSome)
                "CEGIS failed at its measured iteration boundary"
            printfn "  CEGIS minimum successful limit: %d / 128" minimum
    "Z3 synthesizes negative unrestricted coefficients", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "z3-negative-arbitrary-coefficients.koat"))
        let graph = Graph.create system
        let internalEdges =
            Components.findCyclic graph (Scc.analyseFromStart graph)
            |> Array.exactlyOne
            |> fun cyclicComponent -> cyclicComponent.InternalEdges
        match Ranking.tryFindZ3Linear internalEdges with
        | Some ranking ->
            require
                (ranking.Coefficients |> Array.exists (fun coefficient -> coefficient < -1I))
                "Z3 synthesis did not require a negative coefficient outside {-1,0,1}"
            require (Z3Backend.verifyStrictRanking 1000 internalEdges ranking = Valid) "negative ranking was invalid"
        | None -> failwith "Z3 did not synthesize negative unrestricted coefficients"
    "Z3 synthesizes shifted unrestricted coefficients", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "z3-shifted-arbitrary-coefficients.koat"))
        let graph = Graph.create system
        let internalEdges =
            Components.findCyclic graph (Scc.analyseFromStart graph)
            |> Array.exactlyOne
            |> fun cyclicComponent -> cyclicComponent.InternalEdges
        match Ranking.tryFindZ3Linear internalEdges with
        | Some ranking ->
            require (ranking.Constant > 0I) "Z3 synthesis omitted the required positive shift"
            require (Z3Backend.verifyStrictRanking 1000 internalEdges ranking = Valid) "shifted ranking was invalid"
        | None -> failwith "Z3 did not synthesize shifted unrestricted coefficients"
    "Z3 synthesis exceeds finite arity limit", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "z3-seven-variable-ranking.koat"))
        let graph, _, result = Analysis.analyse system
        match result with
        | Yes [| proof |] ->
            require (proof.Ranking.Coefficients.Length = 7) "seven-variable ranking has the wrong arity"
            require
                (Z3Backend.verifyStrictRanking 1000 proof.Component.InternalEdges proof.Ranking = Valid)
                "seven-variable ranking was invalid"
        | _ -> failwith "Z3 did not prove a ranking above the finite arity limit"
    "Z3 reports no single linear ranking", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "z3-no-single-linear-ranking.koat"))
        let graph, _, result = Analysis.analyse system
        let internalEdges =
            Graph.create system
            |> fun createdGraph -> Components.findCyclic createdGraph (Scc.analyseFromStart createdGraph)
            |> Array.exactlyOne
            |> fun cyclicComponent -> cyclicComponent.InternalEdges
        require (Ranking.tryFindZ3Linear internalEdges |> Option.isNone) "Z3 invented a conflicting linear ranking"
        match result with
        | Maybe _ -> ()
        | _ -> failwith "absence of a single linear ranking did not remain MAYBE"
    "transition removal proves mandatory decrease", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "transition-removal.koat"))
        let graph, _, result = Analysis.analyse system
        match result with
        | Yes [| proof |] ->
            require (proof.StrictEdges.Length = 1) "transition-removal proof has the wrong strict edges"
            require (proof.WeakEdges.Length = 1) "transition-removal proof has the wrong weak edges"
            let report = Report.render graph result
            require (report.Contains("weak-only graph: acyclic")) "transition-removal evidence was not reported"
        | _ -> failwith "mandatory strict decrease was not proven"
    "transition removal uses immediate continuation guard", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "immediate-continuation-guard.koat"))
        let _, _, result = Analysis.analyse system
        match result with
        | Yes [| proof |] -> require (proof.Ranking.Coefficients = [| 1I |]) "continuation guard selected the wrong ranking"
        | _ -> failwith "immediate continuation guard did not bound the strict decrease"
    "transition removal rejects weak-only cycle", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "weak-only-cycle.koat"))
        let _, _, result = Analysis.analyse system
        match result with Maybe _ -> () | _ -> failwith "weak-only cycle was unsafely accepted"
    "cycle-dependent lower bound proves decreasing y", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "cycle-dependent-lower-bound.koat"))
        let _, _, result = Analysis.analyse system
        match result with
        | Yes [| proof |] -> require (proof.Ranking.Coefficients = [| 0I; 1I |]) "cycle-dependent proof did not rank y"
        | _ -> failwith "cycle-dependent y lower bound was not proven"
    "unrelated continuation guard cannot bound ranking", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "unrelated-continuation-guard.koat"))
        let _, _, result = Analysis.analyse system
        match result with Maybe _ -> () | _ -> failwith "unrelated y guard was unsafely used to bound x"
    "non-decreasing guarded loop is not ranked", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "non-decreasing.koat"))
        let _, _, result = Analysis.analyse system
        match result with Maybe _ -> () | _ -> failwith "non-decreasing loop was unsafely ranked"
    "obvious non-termination", fun () ->
        let system = parseTestFixture (Path.Combine("generated", "Infinite.koat"))
        let graph, _, result = Analysis.analyse system
        match result with
        | No witness ->
            require (witness.Loop.Source = witness.Loop.Target) "witness is not a self-loop"
            require ((Report.render graph result).Contains("cyclic SCCs: (")) "NO report omitted cyclic SCCs"
        | _ -> failwith "unguarded total self-loop was not NO"
    "unguarded stem to obvious non-termination", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "unguarded-stem.koat"))
        let _, _, result = Analysis.analyse system
        match result with
        | No witness -> require (witness.Stem.Length = 1) "wrong witness stem"
        | _ -> failwith "reachable obvious self-loop was not NO"
    "partial arithmetic is not obvious non-termination", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "partial-arithmetic.koat"))
        let _, _, result = Analysis.analyse system
        match result with Maybe _ -> () | _ -> failwith "partial self-loop was unsafely classified"
    "SCC report groups locations", fun () ->
        let system = parseTestFixture (Path.Combine("analysis", "scc-report.koat"))
        let graph, _, result = Analysis.analyse system
        let report = Report.render graph result
        require (report.Contains("(a, b)") || report.Contains("(b, a)")) "multi-location SCC was not parenthesized"
        require (report.Contains("(c)")) "single-location SCC was not parenthesized"
]

let fixtureExpectations = [
    1, "YES"
    2, "NO"
    3, "YES"
    4, "MAYBE"
    5, "YES"
    6, "YES"
    7, "YES"
    8, "YES"
    9, "YES"
    10, "YES"
    11, "YES"
    12, "MAYBE"
    13, "NO"
    14, "YES"
    15, "YES"
    16, "YES"
]

let fixtureTests =
    fixtureExpectations
    |> List.map (fun (number, expected) ->
        $"test{number}.koat", fun () ->
            let system = parseTestFixture (Path.Combine("cases", $"test{number}.koat"))
            let _, _, result = Analysis.analyse system
            let actual =
                match result with
                | Yes _ -> "YES"
                | No _ -> "NO"
                | Maybe _ -> "MAYBE"
            require (actual = expected) $"expected {expected}, but got {actual}")

let terminationScenarioExpectations = [
    "nested-two-level.koat", "MAYBE"
    "nested-three-level.koat", "MAYBE"
    "tail-recursion-terminating.koat", "YES"
    "tail-recursion-nonterminating.koat", "NO"
    "mutual-recursion-terminating.koat", "YES"
    "mutual-recursion-nonterminating.koat", "MAYBE"
]

let terminationScenarioTests =
    terminationScenarioExpectations
    |> List.map (fun (fileName, expected) ->
        fileName, fun () ->
            let system = parseTestFixture (Path.Combine("termination", fileName))
            let _, _, result = Analysis.analyse system
            let actual =
                match result with
                | Yes _ -> "YES"
                | No _ -> "NO"
                | Maybe _ -> "MAYBE"
            require (actual = expected) $"expected {expected}, but got {actual}")

let tests = unitTests @ fixtureTests @ terminationScenarioTests

[<EntryPoint>]
let main _ =
    let mutable failed = 0
    for name, test in tests do
        try test (); printfn "PASS %s" name
        with error -> failed <- failed + 1; eprintfn "FAIL %s: %s" name error.Message
    if failed = 0 then printfn "all %d tests passed" tests.Length; 0 else 1
