namespace TerminationEngine

/// 1つの引数を選び、符号反転と非負性のための定数シフトを許すランキング関数。
type ProjectionRanking = {
    ArgumentIndex: int
    Sign: bigint
    Offset: bigint
}
