open System
open System.IO
open TerminationEngine

[<EntryPoint>]
let main args =
    if args.Length <> 1 then
        eprintfn "使用方法: termination-engine <input.koat>"
        2
    else
        try
            let system = File.ReadAllText args[0] |> KoatParser.parse
            let graph, _, result = Analysis.analyse system
            printfn "%s" (Report.render graph result)
            0
        with
        | KoatParseException error ->
            eprintfn "%s(%d,%d): %s" args[0] error.Position.Line error.Position.Column error.Message
            1
        | error -> eprintfn "%s" error.Message; 1
