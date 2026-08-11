namespace TerminationEngine

open System.Collections.Generic
open Microsoft.Z3

module Z3Encoding =
    let private map2 mapping left right =
        match left, right with
        | Ok leftValue, Ok rightValue -> Ok(mapping leftValue rightValue)
        | Error error, _
        | _, Error error -> Error error

    type Environment = {
        Context: Context
        Variables: Dictionary<string, Microsoft.Z3.IntExpr>
    }

    let createEnvironment context =
        { Context = context
          Variables = Dictionary<string, Microsoft.Z3.IntExpr>() }

    let private variable environment name =
        match environment.Variables.TryGetValue name with
        | true, value -> value
        | false, _ ->
            let value = environment.Context.MkIntConst name
            environment.Variables.Add(name, value)
            value

    let rec encodeInt environment = function
        | Integer value -> Ok(environment.Context.MkInt(string value) :> ArithExpr)
        | Variable name -> Ok(variable environment name :> ArithExpr)
        | Negate value ->
            encodeInt environment value
            |> Result.map (environment.Context.MkUnaryMinus)
        | Add(left, right) ->
            map2
                (fun leftValue rightValue -> environment.Context.MkAdd(leftValue, rightValue))
                (encodeInt environment left)
                (encodeInt environment right)
        | Subtract(left, right) ->
            map2
                (fun leftValue rightValue -> environment.Context.MkSub(leftValue, rightValue))
                (encodeInt environment left)
                (encodeInt environment right)
        | Multiply(Integer factor, value)
        | Multiply(value, Integer factor) ->
            encodeInt environment value
            |> Result.map (fun encoded -> environment.Context.MkMul(environment.Context.MkInt(string factor), encoded))
        | Multiply _ -> Error "変数同士の乗算は線形整数算術ではありません。"
        | Divide _ -> Error "除算のSMT符号化は未対応です。"
        | Mod _ -> Error "剰余のSMT符号化は未対応です。"

    let encodeLinearForm environment (form: LinearForm) =
        let terms =
            form.Coefficients
            |> Map.toArray
            |> Array.map (fun (name, coefficient) ->
                environment.Context.MkMul(
                    environment.Context.MkInt(string coefficient),
                    variable environment name :> ArithExpr))
        Array.append [| environment.Context.MkInt(string form.Constant) :> ArithExpr |] terms
        |> environment.Context.MkAdd

    let rec encodeBool environment = function
        | Compare(comparison, left, right) ->
            map2 (fun leftValue rightValue ->
                match comparison with
                | Eq -> environment.Context.MkEq(leftValue, rightValue)
                | NotEq -> environment.Context.MkNot(environment.Context.MkEq(leftValue, rightValue))
                | Lt -> environment.Context.MkLt(leftValue, rightValue)
                | Le -> environment.Context.MkLe(leftValue, rightValue)
                | Gt -> environment.Context.MkGt(leftValue, rightValue)
                | Ge -> environment.Context.MkGe(leftValue, rightValue))
                (encodeInt environment left)
                (encodeInt environment right)
        | And(left, right) ->
            map2
                (fun leftValue rightValue -> environment.Context.MkAnd(leftValue, rightValue))
                (encodeBool environment left)
                (encodeBool environment right)
        | Or(left, right) ->
            map2
                (fun leftValue rightValue -> environment.Context.MkOr(leftValue, rightValue))
                (encodeBool environment left)
                (encodeBool environment right)
        | Not value -> encodeBool environment value |> Result.map environment.Context.MkNot
