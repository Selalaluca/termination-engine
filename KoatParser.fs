namespace TerminationEngine

open System.Collections.Generic
open FSharp.Text.Lexing

module KoatParser =
    let private failAt position message =
        raise (KoatParseException { Position = position; Message = message })

    let private variablesInInt expression =
        let rec collect acc = function
            | Integer _ -> acc
            | Variable name -> Set.add name acc
            | Negate value -> collect acc value
            | Add (left, right)
            | Subtract (left, right)
            | Multiply (left, right)
            | Divide (left, right)
            | Mod (left, right) -> collect (collect acc left) right
        collect Set.empty expression

    let private variablesInBool expression =
        let rec collect acc = function
            | Compare (_, left, right) -> Set.union acc (Set.union (variablesInInt left) (variablesInInt right))
            | And (left, right)
            | Or (left, right) -> collect (collect acc left) right
            | Not value -> collect acc value
        collect Set.empty expression

    let private validate system =
        let declared = Set.ofList system.Variables
        if declared.Count <> system.Variables.Length then
            failAt { Line = 1; Column = 1 } "VAR宣言に重複があります。"

        let arities = Dictionary<string, int>()
        let checkTerm (rule: Rule) term =
            // 関数記号の初出時に引数数を記録し、以降の出現が同じarityか検査する。
            match arities.TryGetValue term.Symbol with
            | true, arity when arity <> term.Arguments.Length ->
                failAt rule.Span.Start (sprintf "関数記号%sの引数数が一致しません。" term.Symbol)
            | false, _ -> arities[term.Symbol] <- term.Arguments.Length
            | _ -> ()
            term.Arguments |> List.collect (variablesInInt >> Set.toList)

        for rule in system.Rules do
            let used =
                checkTerm rule rule.Source
                @ checkTerm rule rule.Target
                @ (rule.Guard |> Option.map (variablesInBool >> Set.toList) |> Option.defaultValue [])
            // 規則内で使われる変数のうち、VAR宣言にない最初の名前を報告する。
            match used |> List.tryFind (declared.Contains >> not) with
            | Some name -> failAt rule.Span.Start (sprintf "未宣言の変数です: %s" name)
            | None -> ()

        if not (arities.ContainsKey system.Start) then
            failAt { Line = 2; Column = 1 } (sprintf "開始関数記号%sに対応する規則がありません。" system.Start)
        system

    let parse text =
        let lexbuf = LexBuffer<char>.FromString text
        try
            KoatGrammar.program KoatLexer.token lexbuf |> validate
        with
        | KoatParseException _ as error -> raise error
        | _ ->
            let position = { Line = lexbuf.StartPos.Line + 1; Column = lexbuf.StartPos.Column + 1 }
            failAt position "KoATの構文が正しくありません。"

    let tryParse text =
        try Ok(parse text) with KoatParseException error -> Error error
