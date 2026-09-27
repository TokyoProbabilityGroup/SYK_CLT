# AGENTS.md

## 適用範囲と目的

このファイルは `SYK/CLT/Lemmas/` 以下に適用する。上位の `SYK/AGENTS.md` と `SYK/CLT/AGENTS.md` も適用する。

ここでは数学的規約を重複して書かず、**Lean の探索時に読む量を減らすこと**と、補題ファイルの依存を小さく保つことだけを定める。純粋な再編では、公開宣言の名前・namespace・型・仮定・属性・規格化を変更しない。

## 最優先: declaration-first

ファイルを先頭から全文読まず、まず宣言名と依存箇所を検索する。

1. 目的の宣言名が分かる場合は、その定義と caller を `rg` で検索する。
2. 不明なら、対象ファイルの `theorem` / `lemma` / `def` / `structure` / `namespace` / `section` 行だけを見る。
3. 最初は対象宣言の前後 60--150 行だけ読む。必要な local helper がある場合だけ広げる。
4. 型だけ必要なら、長い proof より `#check`, `#print`, Lean のエラーを優先する。
5. sibling file を念のため全部読むことはしない。

例:

```bash
rg -n 'DECLARATION_NAME' SYK/CLT SYK/Probability SYK/Model
rg -n '^(private )?(theorem|lemma|def|noncomputable def|structure|class) |^namespace |^section ' SYK/CLT/Lemmas
rg -n '^import ' SYK/CLT/Lemmas
```

特に次の三つは、通常の補題利用では全文を読まない。

- `GaussianIBP.lean`: 約 300 KB
- `Tool.lean`: 約 112 KB
- `../Main.lean`: 約 30 KB

## nakajima branch の現在の依存図

以下で `A -> B` は「`B` が `A` を import する」を表す。

```text
CliffordSignParity
        -> GaussianChaos
        -> GaussianHermiteOrthogonality
        -> GaussianHermiteDensity
             + GaussianMomentDetermination
        -> GaussianPolynomialDensity

Main + CliffordSignParity + GaussianHermiteOrthogonality
        -> Preliminaries

Preliminaries + Tool
        -> PartitionDerivatives

Preliminaries + PartitionDerivatives + ConvexDerivatives
        -> CLTComponents

Rademacher   (ほぼ独立)
```

この現行グラフを確認せずに、別 branch の構成を前提として import を変更しない。特に `Preliminaries.lean` は現在 `CLT.Main` を import している。これを解消する場合は、`Setting`, `Z`, `Y` など本当に上流に置くべき定義を小さい基礎 module へ抽出してから caller を更新する。単に import を消したり、定義を複製したりしない。

## 作業別の入口

長いファイルを探索する前に、まず次の公開宣言を入口にする。

- 符号対称性・一次/非対角二次カオス:
  `Setting.Z_sign_gauge`,
  `Setting.Z_firstChaos_eq_zero`,
  `Setting.Y_firstChaos_eq_zero`,
  `Setting.inner_offDiagonal_secondChaos_eq_zero`
  in `Preliminaries.lean`.
- 分配関数の微分:
  `Setting.Z_contDiff_couplings`,
  `Setting.Z_hasDerivAt_beta`,
  `Setting.coordDeriv_Z_eq`,
  `Setting.integral_Z_mul_sq_sub_one_ibp`,
  `Setting.sum_integral_Y_mul_sq_sub_one`
  in `PartitionDerivatives.lean`.
- exact second chaos:
  `Setting.Y_secondChaos_eq`
  in `CLTComponents.lean`.
- 行列指数:
  `MatrixAnalysis.DerivAux.contDiff_tE`,
  `MatrixAnalysis.Matrix.traceExp`,
  `MatrixAnalysis.Matrix.iterDirectionalFDeriv_traceExp_bound`,
  `MatrixAnalysis.Matrix.iterDirectionalFDeriv_traceExp_bound_of_norm_le_one`
  in `Tool.lean`.
- Gaussian--Hermite の一般部分積分は、まず
  `SYK/Probability/GaussianConcentration/Smooth.lean`
  の共有 API を探す。現行 CLT の一般 Hermite IBP のために `GaussianIBP.lean` を最初から読む必要はない。
- Hermite 展開・完全性は
  `GaussianChaos.lean`,
  `GaussianHermiteOrthogonality.lean`,
  `GaussianPolynomialDensity.lean`
  の順に必要な宣言だけ辿る。
- Rademacher 評価は `Rademacher.lean`、凸関数の導関数収束は `ConvexDerivatives.lean` を直接見る。

`ARCHITECTURE.md` と `EDITING_PLAN.md` は、上位 `AGENTS.md` が要求する**該当節だけ**読む。既知の補題を一つ利用するだけの作業で全文を読み直さない。

## ファイルを再編するとき

一つの file は一つの数学的役割または一つの proof layer を担当させる。`Tool.lean`, `Utils.lean`, `Misc.lean` のような新しい倉庫 file は作らない。

目安として 200--500 行程度を好む。800 行を大きく超え、複数の独立した namespace/section を持つ場合は分割候補とする。ただし一つの密接な証明を行数だけで切らない。

### `Tool.lean`

`Tool.lean` は一括で編集せず、少なくとも次の依存 closure ごとに扱う。

```text
singular values / min-max / Ky Fan
Schatten inequalities
positive trace estimates
Duhamel / exp derivative
normalized trace exponential
higher directional derivatives / word bounds
```

`PartitionDerivatives.lean` が実際に使う `traceExp` と `contDiff_tE` の dependency closure を先に特定する。分割時は「宣言を短い wrapper で複製する」のではなく、実装を一つの module に移して importer を更新する。

### `GaussianIBP.lean`

この巨大 file を active CLT dependency に追加する前に、共有 `Probability/GaussianConcentration` に必要な結果が既にないか確認する。現行 branch では Gaussian--Hermite IBP の一般部分は共有側が正式な入口である。

### `Preliminaries.lean`

ここには現在、対称性、Hermite parity の `Setting` への接続、`ZGaussianLp/YGaussianLp`、一次カオス、非対角二次カオスが集まっている。再編するならこの数学的境界で分ける。`Main` の内容をコピーして依存を避けない。

### `CLTComponents.lean`

ここは最終的に「二次カオス」など内容が名前から分かる module 名を好む。`Components` に無関係な後続補題を追加し続けない。

## API 索引を複製しない

補題一覧だけの Lean file や、既存定理を短い proof で再宣言した API file を作らない。これは token 節約ではなく、主張の二重管理と transitive import の増加になる。

代わりに各 module の docstring に、

- module の役割を 1--3 文
- 主な公開 entry point の**宣言名だけ**

を置く。正確な定理文は実装宣言を唯一の source of truth とする。

## import の原則

- 必要な sibling module を直接 import し、偶然の transitive import に依存しない。
- model-independent な結果は可能なら共有 `Probability` / `Model` 側に置き、共有側から CLT を import しない。
- 古い path を残す compatibility shim は自動的に作らない。repo 内 caller を更新できるなら直接更新する。
- aggregate module を作る場合は import-only とし、基礎 module から aggregate module を import しない。

## 移動と検証

一度に一つの coherent block だけ移動する。

1. 公開宣言、private helper、section variables、caller を検索する。
2. dependency closure を新 module へ移す。
3. 宣言名・namespace・型が不変であることを確認する。
4. 直接 importer を更新する。
5. 新 module と直接 consumer を個別に検査する。
6. old path / 重複宣言を `rg` で確認する。
7. 最後に `lake build CLT` を実行する。

再編中に別の数学的問題を見つけても、reorganization と無関係な theorem statement の変更を同じ差分に混ぜない。
