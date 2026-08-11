# Halting Analyzer

KoAT形式の整数遷移系を読み込み、停止性を解析するためのF#プロジェクト。

FsLex/FsYaccによるKoATパーサーと意味検査、および開始位置から到達可能な制御フローのSCC分解を実装している。
現在は、閉路がない場合に加え、すべての到達可能な循環SCCにアフィン射影ランキング関数を発見できた場合も`YES`とする。ガードなしで全域的に定義された自己ループへ同種の経路で到達できれば`NO`、どちらも証明できない循環は`MAYBE`と出力する。

## 必要環境

- .NET SDK 10
- FsLexYacc 11.4.0

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

## 使い方

```powershell
dotnet run --project TerminationEngine.fsproj -- input.koat
```

最終的な出力：

```text
YES    停止を証明した
NO     非停止を証明した
MAYBE  どちらも証明できなかった
```

ランキング関数で`YES`を証明した場合は、循環SCCと採用した証明書も表示する。

```text
YES
cyclic SCCs: (loop)
(loop) ranking: rho(x) = -x + 9 [constant=9, coefficients=[-1]]
```

`NO`と`MAYBE`でも、到達可能な循環SCCを同じ括弧形式で表示する。

構文・意味エラーはファイル名、行、列とともに標準エラーへ出力する。

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

定数`c`は各内部辺のガードから得られる整数下限を使い、ランキング値を非負にする最小値を合成する。現在の方式では、SCC内の全内部遷移で同じアフィン射影が厳密に減少する必要がある。`x + y`のような一般線形ランキング、辞書式ランキング、多相ランキングには未対応。

一般線形ランキングの準備として、係数領域`{-1,0,1}`から非ゼロの係数ベクトルを列挙する処理を実装している。単一変数だけを使う候補を優先し、候補数の指数的増加を抑えるためarityは最大6に制限する。生成した一般線形候補の検証と判定への接続は未実装である。

`LinearRanking`の係数と定数項を遷移規則の引数へ代入し、更新前後の`LinearForm`を構築する処理も実装している。arity不一致と、非ゼロ係数が掛かる非線形式は近似せず拒否する。

一般線形候補について、各内部辺の`rho_before - rho_after`を計算し、差が定数かつ1以上になる場合だけ減少性を受理する。差に状態変数が残る条件付き減少は、SMT検証を導入するまで安全側に不採用とする。一般線形の非負性検証と判定への接続は未実装である。

一般線形候補の係数部分と同じ形の比較をガードから探し、整数下限を抽出して非負性に必要な定数項を合成する処理も実装している。論理積では最も強い下限を採用し、SCC内の全内部辺が要求する定数項の最大値を使用する。係数形が一致しない比較は下限として利用しない。

停止判定では、まず既存のアフィン射影を探索し、失敗した循環SCCだけ一般線形候補を係数の小さい順に検査する。定数項を合成でき、かつ全内部辺でランキング値が1以上減少する最初の候補を証明書として採用する。

全辺での厳密減少に失敗した場合は、非増加＋必須減少によるtransition removalも試す。全内部辺が`Strict`または`Weak`で、少なくとも1本が`Strict`、かつ`Weak`辺だけのグラフが非循環になる候補を受理する。ランキング値の下限を全内部辺のガードから合成できない場合は、安全側に候補を不採用とする。証明書にはStrict辺とWeak辺を保持する。

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
  RankingCertificate.fs        ランキング証明書の型
  RankingVerification.fs       ランキング証明書の検査
  RankingSynthesis.fs          射影ランキング関数の探索
  Ranking.fs                   ランキング解析の公開窓口
  Analysis.fs                  循環SCCの分類と判定の統合
  Report.fs                    判定結果の表示
  Program.fs                   CLI
  TerminationEngine.fsproj     本体プロジェクト
```
