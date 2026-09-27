# AGENTS.md

## 適用範囲

このファイルは `SYK/CLT/Lemmas/` 以下に適用する。上位の `SYK/AGENTS.md` と `SYK/CLT/AGENTS.md` も適用するが、ここでは補題群の探索・分割・import 設計を、エージェントのコンテキスト量を小さく保つことを優先して定める。

このディレクトリの再編だけを依頼された場合、数学的主張そのものを変更しない。既存の公開宣言について、定理文、名前、名前空間、属性、仮定、規格化を保存する。証明の書き換えは、移動に必要な名前解決や import 調整を除いて別作業とする。

## 最優先: declaration-first で読む

大きな Lean ファイルを先頭から全文読まない。特に `GaussianIBP.lean` と `Tool.lean` は、ファイル全体の再編を明示的に行う場合を除き、全文をコンテキストへ入れない。

作業開始時は次の順で対象を絞る。

1. 宣言名が分かっているなら、まず exact search で定義箇所と利用箇所を探す。
2. 宣言名が不明なら、対象ファイルの `theorem` / `lemma` / `def` / `structure` / `namespace` / `section` の行だけを一覧して輪郭を取る。
3. 必要な宣言の前後だけを読む。最初はおおむね 80--150 行で十分とし、ローカル補題を追う必要がある場合だけ範囲を広げる。
4. 証明本文を読む前に caller/importer を検索する。型だけ必要なら `#check`, `#print`, Lean のエラー出力を優先し、長い証明を読まない。
5. 関係する上流宣言だけを辿り、同じファイルの無関係な節や sibling file は読まない。

ローカル環境では、例えば次のような検索を優先する。

```bash
rg -n '^(private )?(theorem|lemma|def|noncomputable def|structure|class) |^namespace |^section ' SYK/CLT/Lemmas
rg -n '\bDECLARATION_NAME\b' SYK
rg -n '^import ' SYK/CLT/Lemmas
```

`ARCHITECTURE.md` や `EDITING_PLAN.md` も、上位の指示で必要な節だけ読む。既知の宣言を利用するだけの作業で、毎回これらを全文読み直さない。

## ファイル設計

一つの Lean ファイルは一つの数学的役割、または一つの証明層を担当させる。名前だけでは内容を推測できない `Tool.lean`, `Utils.lean`, `Misc.lean` のような倉庫ファイルを新たに作らない。

実用上は 200--500 行程度のファイルを好む。800 行を大きく超え、かつ複数の独立した節・名前空間・理論を含むなら分割を優先する。行数だけを目的に、密接に結びついた一つの証明を不自然に分断しない。

各ファイルの先頭の module docstring には、そのファイルの役割と主要な公開 entry point の**宣言名だけ**を短く書く。定理文を別ファイルへコピーして索引を作らない。宣言の唯一の source of truth は実装ファイルとする。

「補題の一覧を短い証明でもう一度書いた API ファイル」は作らない。これは探索時には短く見えても、主張の二重管理と import の不透明化を生む。必要なら aggregate file は import のみとし、宣言探索には各 module docstring と exact search を使う。

## 依存方向

目標の依存方向は次である。

```text
Mathlib / shared Probability / shared Model
                ↓
CLT/Lemmas の model-independent modules
                ↓
CLT/Lemmas の SYK-specific modules
                ↓
CLT/Main と最終定理
```

`CLT/Lemmas/` から `CLT/Main.lean` を import しない。補題が `Main.lean` に置かれた定義を必要とする場合、その定義が本当に上流概念なら小さい upstream module へ移す。下流の `Main` を import して解決しない。

model-independent なガウス解析は、既存の `SYK/Probability/GaussianConcentration/` に同等の結果がないか先に検索する。共有可能なら CLT 内に重複実装せず、共有基盤側へ置く。共有側から CLT への import は作らない。

## 再編の目標

現在のファイル名を機械的に保つことより、数学的なまとまりと探索コストを優先する。ただし純粋な再編では公開宣言名と定理文を変えない。

第一段階の目安は次のような構成である。

```text
CLT/Lemmas/
  Analysis/
    ConvexDerivatives.lean
  Gaussian/
    HermiteCoefficients.lean
    HermiteOrthogonality.lean
    HermiteDensity.lean
    MomentDetermination.lean
    PolynomialDensity.lean
  Matrix/
    SingularValues.lean
    Schatten.lean
    Duhamel.lean
    TraceExp.lean
    WordBounds.lean
  SYK/
    CliffordSignParity.lean
    Rademacher.lean
    Preliminaries.lean
    CLTComponents.lean
```

この木は絶対的な名前指定ではなく、依存層を示す設計目標である。既存 import と公開 API を確認して、より自然な境界があればそちらを選ぶ。

### `GaussianIBP.lean`

このファイルを一つの単位として扱わない。少なくとも次を別の層として扱う。

- 一変数の Gaussian tilt、成長条件、Stein/IBP
- finite-dimensional Hilbert Gaussian の模型・モーメント
- product/Fubini と coordinate-wise Stein step
- Hilbert-space covariance form の最終 IBP

CLT 固有の定義を使わない部分は `Probability/GaussianConcentration` への移動候補とする。既に共有基盤に対応する定理がある場合は、重複証明を温存するより既存 API を使う。

### `Tool.lean`

`Tool.lean` を一括で読む・拡張する前に、各宣言の利用箇所を検索する。少なくとも次は独立した理論として分ける。

- singular values / min-max / Ky Fan
- Schatten inequalities
- positive trace bounds
- Duhamel / matrix exponential differentiation
- normalized trace exponential と高階微分
- word bounds

未使用の大きな節を「将来使うかもしれない」という理由だけで CLT の通常 import 経路へ載せない。削除・共有化が適切かは利用箇所を確認して判断し、純粋なファイル移動と数学的削除を同じ変更で混ぜない。

### `Preliminaries.lean`

`Preliminaries.lean` は下流の `CLT.Main` を import する倉庫にしない。Main に依存する結果は downstream module へ移すか、必要な基礎定義を upstream module へ分離する。

## import の規則

各 module は実際に必要な最小限の sibling module と Mathlib module を import する。ある大きな module を import すると偶然すべて揃う、という transitive import に依存しない。

新しい file boundary を作るときは、まず下流を import しない最小の upstream file を作り、そこから一方向に積む。循環を避けるためだけの wrapper theorem や alias を増やさない。

ファイル移動後に古い path を維持する compatibility shim を自動的に作らない。workspace 内の importer を更新できるなら直接更新する。外部利用との互換性を保つ必要が明示された場合だけ shim を検討する。

## 移動手順

再編は一度に一つの coherent block ずつ行う。

1. 移動対象の公開宣言、private helper、namespace/section 変数、import、caller を列挙する。
2. 新しい module へ一つのまとまりをそのまま移す。
3. 宣言名、namespace、定理文が変わっていないことを確認する。
4. 直接 importer を更新する。
5. 新 module と直接 consumer を個別に Lean で検査する。
6. old file に宣言が重複していないことを確認する。
7. すべての移動後に `lake build CLT` を実行する。

再編中に既存 proof のエラーを見つけても、reorganization と無関係な数学的修正へ自動的に広げない。必要なら別問題として報告する。

## 探索結果の返し方

補題を探す依頼では、最初に「module path + exact declaration name」を返す。長い proof の要約は、ユーザーが必要としている場合だけ付ける。

同じ数学的事実の候補が複数ある場合は、最も上流で一般的な宣言を優先し、CLT 固有 wrapper が必要かを区別する。見つからない場合は、読んだ長大ファイルの量ではなく、検索した宣言名・module・caller の範囲を簡潔に示す。
