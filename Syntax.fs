namespace TerminationEngine

type SourcePosition = { Line: int; Column: int }

type SourceSpan = { Start: SourcePosition; Finish: SourcePosition }

type IntExpr =
    | Integer of int64
    | Variable of string
    | Add of IntExpr * IntExpr
    | Subtract of IntExpr * IntExpr
    | Multiply of IntExpr * IntExpr
    | Divide of IntExpr * IntExpr
    | Mod of IntExpr * IntExpr
    | Negate of IntExpr

type Comparison = Eq | NotEq | Lt | Le | Gt | Ge

type BoolExpr =
    | Compare of Comparison * IntExpr * IntExpr
    | And of BoolExpr * BoolExpr
    | Or of BoolExpr * BoolExpr
    | Not of BoolExpr

type Term = { Symbol: string; Arguments: IntExpr list }

type Rule = {
    Source: Term
    Target: Term
    Guard: BoolExpr option
    Span: SourceSpan
}

type TransitionSystem = {
    Goal: string
    Start: string
    Variables: string list
    Rules: Rule list
}

type ParseError = { Position: SourcePosition; Message: string }

exception KoatParseException of ParseError
