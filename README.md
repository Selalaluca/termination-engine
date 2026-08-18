# termination-engine

KoAT形式の整数遷移系を読み込み、停止性を解析するためのF#プロジェクト。

FsLex/FsYaccによるKoATパーサーと意味検査、および開始位置から到達可能な制御フローのSCC分解を実装している。
現在は、閉路がない場合に加え、すべての到達可能な循環SCCにアフィン射影ランキング関数を発見できた場合も`YES`とする。ガードなしで全域的に定義された自己ループへ同種の経路で到達できれば`NO`、どちらも証明できない循環は`MAYBE`と出力する。

## 必要環境

- .NET SDK 10
- FsLexYacc 11.4.0
- Microsoft.Z3 4.12.2

## ビルド

```powershell
dotnet build TerminationEngine.fsproj
```

FsLex/FsYaccがビルド時に次のファイルからLexerとParserを生成する。

```text
KoatLexer.fsl   -> obj/Generated/KoatLexer.fs
KoatGrammar.fsy -> obj/Generated/KoatGrammar.fs
```

生成された`.fs`は編集しない。字句や文法を変更する場合は`.fsl`または`.fsy`を編集する。

## テスト

```powershell
dotnet run --project tests/TerminationEngine.Tests.fsproj
```

KoATで表現できる入力はF#コードへ埋め込まず、次のfixtureフォルダーから読み込む。

```text
tests/fixtures/
  parser/    正常な構文と演算子優先順位
  invalid/   構文エラーと意味エラー
  analysis/  SCC、ランキング、SMT、非停止解析
  generated/ cil2koatが生成したKoATの独立スナップショット
  cases/     test1.koat ～ test16.koatの総合判定
  termination/ 2重・3重・4重ループ、独立境界の入れ子ループ、末尾再帰、相互再帰
```

F#側には期待する構文木、証明情報、または`YES`／`NO`／`MAYBE`だけを記述する。

## 使い方

```powershell
dotnet run --project TerminationEngine.fsproj -- [-t] [-i] [-s] input.koat
```

- `-t`: 停止性判定時間と総処理時間を標準エラーへ表示する。
- `-i`: 循環SCC、ランキング証明、非停止証拠などの詳細情報を表示する。
- `-s`: SMT問い合わせとCEGIS過程を標準エラーへ表示する。SMT-LIB相当の制約、SAT／UNSAT／UNKNOWN、係数モデル、反例状態、反復番号、候補の採否を含む。
- オプションなし: `YES`、`NO`、`MAYBE`の判定結果だけを表示する。

最終的な出力：

```text
YES    停止を証明した
NO     非停止を証明した
MAYBE  どちらも証明できなかった
```

`-i`を指定し、ランキング関数で`YES`を証明した場合は、循環SCCと採用した証明書も表示する。

```text
YES
cyclic SCCs: (loop)
(loop) ranking method: projection
(loop) ranking: rho(x) = -x + 9 [constant=9, coefficients=[-1]]
```

`ranking method`には、最終的に成立して採用された探索方式として`projection`、`general-linear`、`z3-linear`、`transition-removal`、または`lexicographic`を表示する。不成立だった候補は表示しない。

単一ランキングで証明できない入れ子ループには、Strict辺を段階的に除去する辞書式ランキングを使用する。各段では残余の循環に属する辺だけを次段へ渡し、最大8段まで探索する。係数`{-1,0,1}`の有限探索で失敗した段では、既存のCEGISを再利用して、全辺で非増加かつ指定辺で厳密減少する任意整数係数をZ3で合成する。合成候補は各辺についてZ3で再検証する。成立時は`ranking method: lexicographic`と各段の合成方式、係数、Strict辺、Weak辺を`-i`で表示する。

`-i`を指定した場合、`NO`と`MAYBE`でも到達可能な循環SCCを同じ括弧形式で表示する。

構文・意味エラーはファイル名、行、列とともに標準エラーへ出力する。

`-t`を指定すると、`Analysis.analyse`による停止性判定時間と、ファイル読み込みからレポート生成までの総処理時間を計測し、標準エラーへミリ秒単位で出力する。総処理時間にはコンソールへの出力時間を含めない。

```text
停止性判定時間: 12.345 ms
総処理時間: 15.678 ms
```

判定結果は従来どおり標準出力へ出すため、結果だけをリダイレクトする既存の利用方法には影響しない。

```text
input.koat(5,7): KoATの構文が正しくありません。
```

終了コード:

| コード | 意味 |
|---:|---|
| `0` | 解析成功 |
| `1` | 読み込み、構文、意味検査の失敗 |
| `2` | CLI引数の誤り |

## 対応するKoAT形式

```text
(GOAL TERMINATION)
(STARTTERM (FUNCTIONSYMBOLS eval))
(VAR x y)
(RULES
  eval(x,y) -> loop(x,y)
  loop(x,y) -> loop(x - 1,y + 1) [x > 0]
)
```

対応する要素:

- `GOAL`、`STARTTERM`、`FUNCTIONSYMBOLS`、`VAR`、`RULES`
- 整数、変数、単項マイナス
- 加算、減算、乗算、除算、剰余、括弧
- `=`、`!=`、`<`、`<=`、`>`、`>=`
- `!`、`&&`、`||`
- 省略可能な角括弧形式のガード
- `#`から行末までのコメント

量化とKoATの他方言にある構文には未対応。除算と剰余は構文木へ保持するが、停止性解析上の意味付けは未実装。

## アフィン射影ランキング関数

循環SCCの停止証明では、状態の引数を1つ選ぶ次のランキング関数を探索する。

```text
rho(x1,...,xn) = xi + c
rho(x1,...,xn) = -xi + c
```

候補がSCC内のすべての内部遷移について次を満たす場合、そのSCCは停止すると判定する。

1. ガードからランキング値が非負であると確認できる。
2. 遷移によってランキング値が1以上減少する。

例:

```text
loop(x) -> loop(x - 1) [x > 0]  # rho = x
loop(x) -> loop(x + 1) [x < 0]  # rho = -x
loop(x) -> loop(x + 1) [x < 10] # rho = 9 - x
```

非負性は、論理積に含まれる線形な比較から保守的に確認する。候補探索では定数倍を含む線形式を扱えるが、変数同士の乗算、除算、剰余、論理和などについて証明できない場合は`YES`とせず`MAYBE`に残す。

定数`c`は各内部辺のガードから得られる整数下限を使い、ランキング値を非負にする最小値を合成する。SCC内の全内部遷移で同じランキング関数が厳密に減少する方式に加え、後述のtransition removalにも対応する。辞書式ランキングと多相ランキングには未対応。

一般線形ランキングでは、係数領域`{-1,0,1}`から非ゼロの係数ベクトルを列挙する。単一変数だけを使う候補を優先し、候補数の指数的増加を抑えるためarityは最大6に制限する。`x + y + c`のような候補も停止判定へ接続済みである。

`LinearRanking`の係数と定数項を遷移規則の引数へ代入し、更新前後の`LinearForm`を構築する処理も実装している。arity不一致と、非ゼロ係数が掛かる非線形式は近似せず拒否する。

一般線形候補の厳密減少はZ3で検証する。各内部辺について`guard && rho_before < 0`と`guard && rho_before < rho_after + 1`を反例問い合わせとして送り、両方が`UNSAT`の場合だけ受理する。このため`loop(x) -> loop(0) [x > 0]`のように差へ状態変数が残る更新も証明できる。問い合わせのタイムアウトは1秒で、`SAT`は候補不成立、`UNKNOWN`や未対応式は証明不能として扱う。

Z3Backendは、strict／weak検証、CEGIS用の具体サンプル、strict／transition removalの反例検査結果を解析単位でキャッシュする。キャッシュキーには検証種別、タイムアウト、辺、ランキング、不変条件、辺集合を含め、同じ論理問い合わせだけを再利用する。Z3のContextやASTはキャッシュせず、解析開始時にキャッシュをクリアする。

独立した処理は.NETのスレッドプールを使って並列化する。具体的には、複数の循環SCCの証明探索、複数辺のZ3サンプル取得、strict／weak検証を並列に実行する。辺が1本以下の場合は通常の逐次処理にして並列化の固定費を避ける。各Z3問い合わせは専用のContextを生成し、共有するキャッシュは`ConcurrentDictionary`で保護する。反例探索の辺走査は、最初の反例を返す決定性と不要な問い合わせ削減を保つため逐次のままとする。`-s`のSMTトレースはロックで出力とイベント番号を直列化する。

Z3への変換対象は線形整数算術である。変数同士の乗算、除算、剰余は近似せず拒否するため、それらを含む証明条件から誤って`YES`を返すことはない。

一般線形候補の係数部分と同じ形の比較をガードから探し、整数下限を抽出して非負性に必要な定数項を合成する処理も実装している。論理積では最も強い下限を採用し、SCC内の全内部辺が要求する定数項の最大値を使用する。係数形が一致しない比較は下限として利用しない。

停止判定では、まず既存のアフィン射影を探索し、失敗した循環SCCだけ一般線形候補を係数の小さい順に検査する。定数項を合成でき、かつ全内部辺でランキング値が1以上減少する最初の候補を証明書として採用する。

有限候補でも失敗した場合は、Z3によるCEGIS（反例誘導合成）で係数と定数項を整数変数として合成する。係数は`{-1,0,1}`へ制限しない。まず各遷移の具体状態から係数に関する線形制約を解き、得た候補について既存の全状態反例検査を行う。反例が見つかれば、その状態の非負性・減少性制約を追加して再合成する。

例えば、次の2更新を持つループでは、小係数候補ではなく`rho(x,y) = 3*x + 2*y`を合成する。

```text
loop(x,y) -> loop(x - 1,y + 1) [3*x + 2*y > 0]
loop(x,y) -> loop(x + 1,y - 2) [3*x + 2*y > 0]
```

合成候補は必ず独立したZ3反例検査を通過した場合だけ証明書として採用する。CEGISは最大128反復、各Z3問い合わせは1秒であり、`UNKNOWN`、未対応式、反復上限では証明成功にせず`MAYBE`へ残す。このため任意整数係数を探索できるが、線形ランキングの完全な決定手続きではない。

全辺での厳密減少に失敗した場合は、非増加＋必須減少によるtransition removalも試す。全内部辺が`Strict`または`Weak`で、少なくとも1本が`Strict`、かつ`Weak`辺だけのグラフが非循環になる候補を受理する。ランキング値の下限を全内部辺のガードから合成できない場合は、安全側に候補を不採用とする。証明書にはStrict辺とWeak辺を保持する。

現在、Z3による反例検査は全内部辺がStrictになるランキング経路へ適用する。transition removalは、Weak辺の非循環性と入口条件の限定伝播を含む専用の構文的検査を使う。

Strict辺自身のガードから下限を得られない場合は、その直後にSCC内で実行を継続する全内部辺のガードを調べる。全ての直後内部辺が同じランキング式の下限を与える場合、その最弱下限をStrict辺の実行前にも利用する。出口へ進む実行は有限なので対象外とする。複数段のWeak経路を越えたガード逆伝播は未対応である。

複数の到達可能な循環SCCがある場合は、すべてのSCCを証明できたときだけ全体を`YES`とする。

## 処理の流れ

```text
.koat文字列
  -> KoatLexer.fsl（字句解析）
  -> KoatGrammar.fsy（構文解析）
  -> TransitionSystem（型付き内部表現）
  -> KoatParser.fs（意味検査）
  -> Graph.fs（制御フローグラフ）
  -> Scc.fs（開始位置からTarjan法）
  -> Components.fs（循環SCCと入出辺の構築）
  -> ExpressionAnalysis.fs（式と規則の全域性検査）
  -> NonTermination.fs（自明な非停止証明）
  -> LinearArithmetic.fs（アフィン整数式への安全な変換）
  -> Z3Encoding.fs / Z3Backend.fs（線形整数算術の反例検査）
  -> RankingVerification.fs（ランキング証明書の検査）
  -> RankingSynthesis.fs（射影ランキング関数の探索）
  -> Ranking.fs（ランキング解析の公開窓口）
  -> Analysis.fs（循環SCCの分類と判定の統合）
  -> Report.fs（YES、NO、MAYBE）
```

パーサーは規則ごとに元ファイルの行・列を保持する。これは将来、停止性の判定理由や非停止経路を入力規則へ対応付けるために使用する。

意味検査では次を確認する。

- `VAR`宣言に重複がない
- 式で使う変数が宣言済みである
- 同じ関数記号の引数数が一貫している
- 開始関数記号に対応する規則が存在する

## コードからの利用

例外を使う場合:

```fsharp
let system = KoatParser.parse text
```

エラーを値として受け取る場合:

```fsharp
match KoatParser.tryParse text with
| Ok system -> printfn "%d rules" system.Rules.Length
| Error error ->
    printfn "%d:%d %s" error.Position.Line error.Position.Column error.Message
```

# ファイル構成

```text
termination-engine/
  Syntax.fs                    構文木と遷移系の型
  KoatLexer.fsl                FsLex字句規則
  KoatGrammar.fsy              FsYacc文法規則
  KoatParser.fs                パーサーFacadeと意味検査
  Graph.fs                     制御フローグラフ構築
  Scc.fs                       開始位置からのTarjan SCC分解
  Components.fs                循環SCCと入出辺の構築
  ExpressionAnalysis.fs        式と規則の共通解析
  NonTermination.fs            自明な非停止証明
  LinearArithmetic.fs          bigintによるアフィン整数式の表現と変換
  Smt.fs                       SMT検証結果の共通型
  Z3Encoding.fs                構文木と線形式のZ3式への変換
  Z3Backend.fs                 ランキング条件の反例問い合わせ
  RankingCertificate.fs        ランキング証明書の型
  RankingVerification.fs       ランキング証明書の検査
  RankingSynthesis.fs          射影ランキング関数の探索
  Ranking.fs                   ランキング解析の公開窓口
  Analysis.fs                  循環SCCの分類と判定の統合
  Report.fs                    判定結果の表示
  Program.fs                   CLI
  TerminationEngine.fsproj     本体プロジェクト
```
