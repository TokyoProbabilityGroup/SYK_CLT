# AGENTS.md

## 適用範囲

このファイルは `SYK/SYK_model/` 以下に適用する。workspace ルートの
`AGENTS.md` と `SYK/AGENTS.md` の規則も引き続き適用する。

## 作業前に読む文書

模型の定義または公開 API を変更する前に、次を確認する。

1. `ARCHITECTURE.md`
2. `EDITING_PLAN.md`
3. `../lectureNotes/note.tex` の finite-dimensional SYK model に関する箇所
4. `../CLT/refs/sections/introduction.tex` の `subsec:SYK-model`
5. `model.txt`（historical blueprint としてのみ参照する）
6. 変更する識別子を利用するすべての Lean file

## 役割と source of truth

このディレクトリは複数の研究課題が共有する有限次元 SYK 模型の API を提供する。
一般の有限次元模型の規約は lecture notes、CLT 固有の追加条件と normalization は
CLT 原稿、実装済み API の正確な型と検証状態は Lean source を source of truth とする。
`model.txt` は現行仕様ではなく、非負実温度と raw trace を中心にした初期案である。
これらが一致しない場合は黙って統合せず、相違を報告する。

lecture notes の large-`N` diagrammatics、Schwinger--Dyson equation、conformal
limit、Schwarzian theory などの heuristic statement を finite-`N` Lean theorem の
根拠として使用しない。

## 保護する模型規約

明示的な承認なしに次を変更しない。

- Majorana relation `ψ i * ψ j + ψ j * ψ i = 2 δᵢⱼ` と `ψ i ^ 2 = 1`
- Majorana generator の self-adjointness
- canonical increasing order による interaction product
- even `q` に対する phase `Complex.I ^ (q / 2)`
- coupling variance `(q - 1)! / N ^ (q - 1)`
- Gibbs exponential の符号 `exp (-z H)` とその `z = β` specialization
- normalized trace と unnormalized trace の区別
- interaction order、fermion number、inverse temperature の型と量化範囲

tuple で書かれた interaction label と `q`-element `Finset` の対応では、canonical
increasing order を明示する。共有模型では even `q >= 2` を扱い、`q >= 4`、high
temperature、Gaussian chaos、CLT などの課題固有条件を基本構造へ組み込まない。

## Layer の境界

abstract `MajoranaSystem`、concrete finite matrix realization、deterministic
Hamiltonian、Gaussian disorder、matrix thermodynamics を区別する。abstract Majorana
relations だけから従う結果と、irreducibility、matrix dimension、normalized-trace
orthogonalityを必要とする結果を混同しない。

有限座標 Euclidean space 上の汎用 Gaussian concentration は
`SYK/Probability/GaussianConcentration/` に完全分離する。Gaussian coupling の
SYK specialization は共有模型側に置くが、CLT 固有の chaos projection や漸近定理は
置かない。normalized trace と raw trace には異なる名前を使い、暗黙の定数倍として
扱わない。

## 複素温度と physical layer

analytic layer は `z : ℂ` に対する normalized partition function、entire 性、複素微分を
扱う。これらに positivity を要求しない。`Z z ≠ 0` を必要とする logarithmic derivative
または quotient では仮定を theorem statement に明記する。これは全平面では偽であり、
将来は具体的な zero-free region の theorem から供給する。

physical layer は `β : ℝ≥0` に限定し、partition positivity、thermal density、Gibbs
expectation、real log-partition を扱う。complex temperature に density-matrix 性を
一般化しない。standard Majorana matrix realization と、その dimension・normalized-trace
orthogonality は abstract `MajoranaSystem` と分離して提供する。

再設計後の目標 module path は `SYK.SYKModel` である。移行時にはこの `AGENTS.md` も
`SYK/SYKModel/` へ移す。SpinGlass repository は generic/concrete layer 分離の参考資料と
するが、明示的な承認なしに Lake dependency を追加したりコードを複製したりしない。

## 公開 API の変更

公開 definition、structure field、theorem statement を変更する前に `rg` で全 consumer
を確認し、型、normalization、import graph への影響を説明する。現在の移行では
`../Annealed_FE/` は編集対象外であり、旧 API の削除による同 library の一時的破損は
承認済みである。ただし破損した識別子と検証結果を列挙し、それ以外の consumer を
壊さない。

`sorry`、`admit`、`axiom` または同等の未検証な仮定を導入しない。CLT の未証明
statement に対する個別の許可は、このディレクトリには適用しない。

## 検証

変更した各 Lean file を workspace ルートから `lake env lean` で検査し、続いて
`lake build SYK_model` と移行済み consumer の最小 target を実行する。workspace 全体に
影響する変更では `lake build` も実行し、`Annealed_FE` に限定された既知の失敗と、
許容されない新規 error を区別して報告する。重要な theorem では `#print axioms` を
確認する。
