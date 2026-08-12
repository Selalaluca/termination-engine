open System
open System.Diagnostics
open System.IO
open TerminationEngine

[<EntryPoint>]
let main args =
    let showTime = args |> Array.contains "-t"
    let showInfo = args |> Array.contains "-i"
    let unknownOptions =
        args
        |> Array.filter (fun argument -> argument.StartsWith("-") && argument <> "-t" && argument <> "-i")
    let inputPaths = args |> Array.filter (fun argument -> argument <> "-t" && argument <> "-i")

    if unknownOptions.Length > 0 || inputPaths.Length <> 1 then
        eprintfn "使用方法: termination-engine [-t] [-i] <input.koat>"
        if unknownOptions.Length > 0 then
            eprintfn "不明なオプション: %s" (String.concat ", " unknownOptions)
        2
    else
        try
            let totalStopwatch = Stopwatch.StartNew()
            let inputPath = inputPaths[0]
            let system = File.ReadAllText inputPath |> KoatParser.parse
            let analysisStopwatch = Stopwatch.StartNew()
            let graph, _, result = Analysis.analyse system
            analysisStopwatch.Stop()
            let report =
                if showInfo then Report.render graph result
                else Report.renderVerdict result
            totalStopwatch.Stop()
            printfn "%s" report
            if showTime then
                eprintfn "判定時間: %.3f ms" analysisStopwatch.Elapsed.TotalMilliseconds
                eprintfn "総処理時間: %.3f ms" totalStopwatch.Elapsed.TotalMilliseconds
            0
        with
        | KoatParseException error ->
            eprintfn "%s(%d,%d): %s" inputPaths[0] error.Position.Line error.Position.Column error.Message
            1
        | error -> eprintfn "%s" error.Message; 1
