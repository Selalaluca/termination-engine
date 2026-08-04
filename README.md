# Halting Analyzer

KoAT形式の整数遷移系を読み込み、停止性を解析するためのF#プロジェクト。

FsLex/FsYaccによるKoATパーサーと意味検査、および開始位置から到達可能な制御フローのSCC分解を実装している。
現在は閉路がなければ(つまり全体の遷移グラフがDAGなら)`YES`、循環が残れば`MAYBE`と判定する。`NO`の証明は未実装。

## 必要環境

- .NET SDK 10
- NuGetから復元されるFsLexYacc 11.4.0

## ビルド

ワークスペースのルートから実行する。

```powershell
dotnet build termination-engine\TerminationEngine.fsproj
```

FsLex/FsYaccがビルド時に次のファイルからLexerとParserを生成する。

```text
KoatLexer.fsl   -> obj/Generated/KoatLexer.fs
KoatGrammar.fsy -> obj/Generated/KoatGrammar.fs
```

生成された`.fs`は編集しない。字句や文法を変更する場合は`.fsl`または`.fsy`を編集する。

## CLI

```powershell
dotnet run --project termination-engine\TerminationEngine.fsproj -- input.koat
```

例:

```powershell
dotnet run --project termination-engine\TerminationEngine.fsproj -- cil2koat\tests\golden\Linear.koat
```

非循環入力の出力:

```text
YES
```

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

## 処理の流れ

```text
.koat文字列
  -> KoatLexer.fsl（字句解析）
  -> KoatGrammar.fsy（構文解析）
  -> TransitionSystem（型付き内部表現）
  -> KoatParser.fs（意味検査）
  -> Graph.fs（制御フローグラフ）
  -> Scc.fs（開始位置からTarjan法）
  -> Analysis.fs（循環SCCの分類）
  -> Report.fs（YESまたはMAYBE）
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

## テスト

```powershell
dotnet run --project termination-engine\tests\TerminationEngine.Tests.fsproj
```

現在のテスト対象:

- `cil2koat`が生成したKoATファイル
- コメントと演算子の優先順位
- 規則の入力位置
- 未宣言変数
- 関数記号の引数数不一致
- 構文エラーの位置
- 除算・剰余の優先順位と結合
- 到達不能な循環の除外
- 複数ノードSCCと自己ループSCC

## ファイル構成

```text
termination-engine/
  Syntax.fs                    構文木と遷移系の型
  KoatLexer.fsl                FsLex字句規則
  KoatGrammar.fsy              FsYacc文法規則
  KoatParser.fs                パーサーFacadeと意味検査
  Graph.fs                     制御フローグラフ構築
  Scc.fs                       開始位置からのTarjan SCC分解
  Analysis.fs                  循環SCCの分類と初期判定
  Report.fs                    判定結果の表示
  Program.fs                   CLI
  TerminationEngine.fsproj     本体プロジェクト
  tests/
    Program.fs                 テスト本体
    TerminationEngine.Tests.fsproj
```

最終的な出力は次のいずれかになる。

```text
YES    停止を証明した
NO     非停止を証明した
MAYBE  どちらも証明できなかった
```
