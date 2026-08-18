namespace TerminationEngine

open System
open System.Collections

/// -s指定時だけ、SMT/CEGISの探索過程を標準エラーへ表示する。
module SmtTrace =
    let mutable private enabled = false
    let mutable private sequence = 0L
    let private traceLock = obj ()

    let start () =
        lock traceLock (fun () ->
            enabled <- true
            sequence <- 0L
            eprintfn "[SMT] trace started")

    let rec private renderValue (value: obj) =
        match value with
        | null -> "null"
        | :? string as text -> text
        | :? IEnumerable as values ->
            values
            |> Seq.cast<obj>
            |> Seq.map renderValue
            |> String.concat ", "
            |> sprintf "[%s]"
        | other -> string other

    let emit eventType (fields: (string * obj) list) =
        lock traceLock (fun () ->
            if enabled then
                sequence <- sequence + 1L
                let ordinary, large =
                    fields |> List.partition (fun (key, _) -> key <> "smtLib")
                let details =
                    ordinary
                    |> List.map (fun (key, value) -> sprintf "%s=%s" key (renderValue value))
                    |> String.concat " "
                eprintfn "[SMT %04d] %s%s" sequence eventType (if details = "" then "" else " " + details)
                large
                |> List.iter (fun (_, value) ->
                    eprintfn "[SMT %04d] query:" sequence
                    string value
                    |> fun text -> text.Replace("\r", "").Split('\n')
                    |> Array.filter (String.IsNullOrWhiteSpace >> not)
                    |> Array.iter (eprintfn "    %s")))

    let stop () =
        lock traceLock (fun () ->
            if enabled then eprintfn "[SMT] trace finished (%d events)" sequence
            enabled <- false)
