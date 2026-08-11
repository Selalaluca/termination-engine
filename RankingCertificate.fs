namespace TerminationEngine

/// 1つの引数を選び、符号反転と非負性のための定数シフトを許すランキング関数。
type ProjectionRanking = {
    ArgumentIndex: int
    Sign: bigint
    Offset: bigint
}

/// どの循環成分を、どのランキング関数で証明したかを保持する。
type RankingProof = {
    Component: CyclicComponent
    Ranking: ProjectionRanking
}
