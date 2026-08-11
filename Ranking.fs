namespace TerminationEngine

module Ranking =
    /// 候補合成の実装詳細を公開APIから隠すための窓口。
    let tryFindProjection = RankingSynthesis.tryFindProjection
    let tryFind = RankingSynthesis.tryFind
