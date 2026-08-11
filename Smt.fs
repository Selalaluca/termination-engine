namespace TerminationEngine

type SmtResult =
    | Sat
    | Unsat
    | Unknown of string

type SmtVerificationResult =
    | Valid
    | Invalid
    | Inconclusive of string
