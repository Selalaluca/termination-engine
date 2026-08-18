# termination-engine

KoAT形式の整数遷移系を読み込み、停止性を解析するF#プログラムです。

## 判定

- YES: 到達可能なすべての循環SCCの停止を証明
- NO: 非停止の具体的な証拠を発見
- MAYBE: 証明できない循環SCCが残った

## 必要環境

- .NET SDK 10
- FsLexYacc 11.4.0
- Microsoft.Z3 4.12.2

## 使い方

~~~powershell
dotnet run --project .\termination-engine\TerminationEngine.fsproj -- [-t] [-i] [-s] input.koat
~~~

~~~bash
dotnet run --project ./termination-engine/TerminationEngine.fsproj -- [-t] [-i] [-s] input.koat
~~~

- -t: 判定時間と総処理時間を表示
- -i: SCCとランキング証明の詳細を表示
- -s: Z3／CEGISのトレースを表示

`--project`で実行対象のプロジェクトを指定し、続く`--`より後ろをtermination-engineの引数として渡します。

## ビルド&テスト

以下のコマンドはすべてリポジトリのルートで実行

- Windows(Powershell)

~~~powershell
dotnet build .\termination-engine\TerminationEngine.fsproj
dotnet run --project .\termination-engine\tests\TerminationEngine.Tests.fsproj
~~~


- Linux(Bash)

~~~bash
dotnet build ./termination-engine/TerminationEngine.fsproj
dotnet run --project ./termination-engine/tests/TerminationEngine.Tests.fsproj
~~~

## 解析の流れ

1. CLIが入力ファイルを読み込む（Program.fs）
2. KoATを字句・構文解析し、遷移系を構築する（KoatLexer.fsl、KoatGrammar.fsy、KoatParser.fs、Syntax.fs）
3. 遷移系から制御フローグラフを構築する（Graph.fs）
4. 開始位置から到達可能なSCCと循環成分を抽出する（Scc.fs、Components.fs）
5. 式の対応可否と線形性を確認する（ExpressionAnalysis.fs、LinearArithmetic.fs）
6. ガードから不変条件を抽出し、CFG上へ伝播する（InvariantAnalysis.fs）
7. 自明な非停止証拠を探索する（NonTermination.fs）
8. 射影・一般線形・辞書式ランキングを合成・検証する（Ranking.fs、RankingSynthesis.fs、RankingVerification.fs、RankingCertificate.fs）
9. 必要な反例検査とCEGISをZ3で実行する（Z3Encoding.fs、Z3Backend.fs、Smt.fs、SmtTrace.fs）
10. SCCごとの結果を全体のYES／NO／MAYBEへ統合する（Analysis.fs）
11. 判定結果と証明情報を表示する（Report.fs、Program.fs）

不変条件の伝播は、線形なガードとアフィン更新だけを対象にした保守的な解析です。合流点では全経路に共通する条件だけを残します。

## Z3

Z3の問い合わせ結果は、解析中だけキャッシュします。

- strict／weakランキング検証
- CEGIS用サンプル
- ランキング反例検査

Z3のContextやASTはキャッシュせず、解析開始時にキャッシュを消去します。

## マルチスレッド化

独立した処理を Array.Parallel.map で並列化しています。これは手動でThreadを生成する方式ではなく、.NETのThreadPoolを利用する方式です。

- 独立した循環SCCの証明探索
- 独立した辺のZ3サンプル取得
- strict／weak候補の辺ごとの検証

各Z3問い合わせは専用のContextを使います。共有キャッシュは ConcurrentDictionary、SMTトレースの出力はロックで保護しています。CEGISの反例探索は結果の決定性を保つため逐次処理です。

## 対応する式

整数、変数、加減算、乗算、除算、剰余、比較、!、&&、||に対応しています。Z3による停止証明では線形整数算術だけを扱い、未対応の非線形式は安全側に MAYBE とします。

## ファイル構成

### 本体

| ファイル | 役割 |
|---|---|
| TerminationEngine.fsproj | 本体プロジェクト、依存パッケージ、コンパイル順、Lexer／Parser生成設定 |
| KoatLexer.fsl | KoATの字句解析規則 |
| KoatGrammar.fsy | KoATの構文解析規則 |
| Syntax.fs | 式、ガード、規則、遷移系などのデータ型 |
| KoatParser.fs | 生成Lexer／Parserの呼び出し、意味検査、エラー位置の整理 |
| Graph.fs | 遷移系から制御フローグラフを構築 |
| Scc.fs | 開始位置から到達可能なSCCをTarjan法で抽出 |
| Components.fs | 循環SCC、内部辺、入口辺、出口辺を整理 |
| ExpressionAnalysis.fs | 式の変数、全域性、Z3対応可否などを解析 |
| NonTermination.fs | 自明な非停止経路を検出 |
| LinearArithmetic.fs | 線形整数式、ランキング関数の代入、係数処理 |
| Smt.fs | Z3検証結果の共通型 |
| SmtTrace.fs | SMT／CEGISトレースの出力とイベント番号管理 |
| Z3Encoding.fs | 内部表現をZ3の整数式へ変換 |
| Z3Backend.fs | Z3反例検査、サンプル取得、問い合わせキャッシュ、辺並列化 |
| InvariantAnalysis.fs | ガードから不変条件を抽出し、CFG上で保守的に伝播 |
| RankingCertificate.fs | ランキング証明書とStrict／Weak辺の型 |
| RankingVerification.fs | 構文的なランキング減少、下限、遷移除去の検証 |
| RankingSynthesis.fs | 射影・一般線形・CEGIS・辞書式ランキングの合成 |
| Ranking.fs | ランキング探索機能の公開窓口 |
| Analysis.fs | SCCごとの非停止判定、ランキング探索、全体結果の統合 |
| Report.fs | YES／NO／MAYBEと詳細証明の表示 |
| Program.fs | CLI引数、入力読み込み、時間計測、終了コード |
| README.md | 本プロジェクトの説明と実行方法 |
| .gitignore | ビルド生成物などをGit管理から除外 |

### テスト

| パス | 役割 |
|---|---|
| tests/TerminationEngine.Tests.fsproj | テスト用プロジェクト。本体プロジェクトを参照 |
| tests/Program.fs | パーサー、SCC、ランキング、Z3、統合判定を実行するテストランナー |
| tests/fixtures/parser/ | 正常な構文、演算子優先順位、コメントの入力 |
| tests/fixtures/invalid/ | 構文エラー、未宣言変数、引数数不一致の入力 |
| tests/fixtures/analysis/ | SCC、不変条件、ランキング、Z3、非停止解析の入力 |
| tests/fixtures/generated/ | cil2koatが生成したKoATのスナップショット |
| tests/fixtures/cases/ | test1.koat〜test16.koatの総合ケース |
| tests/fixtures/termination/ | 入れ子ループ、CEGIS、末尾再帰、相互再帰などの停止性ケース |
