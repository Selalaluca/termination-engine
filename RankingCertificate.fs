namespace TerminationEngine

/// 引数位置ごとの係数と定数項からなる一般線形ランキング証明書。
type LinearRanking = {
    Constant: bigint
    Coefficients: bigint array
}

/// どの循環成分を、どのランキング関数で証明したかを保持する。
type RankingProof = {
    Component: CyclicComponent
    Ranking: LinearRanking
}
