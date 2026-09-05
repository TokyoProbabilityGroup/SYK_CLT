# AGENTS.md

## 適用範囲

このファイルは `SYK/Probability/GaussianConcentration/` 以下に適用する。workspace root と
`SYK/AGENTS.md` の規則も適用する。この directory は SYK 模型から独立した、有限次元
Euclidean Gaussian concentration の backend である。

## 独立性

statement と import graph に `ModelParameters`、`InteractionIndex`、`CouplingSpace`、`N`、
`q`、Majorana operator、Hamiltonian、partition function を導入しない。任意の finite
coordinate type `ι` と `EuclideanSpace ℝ ι` に量化する。

この backend は `SYKModel`、`SuperConcentration`、`CLT` を import しない。SYK coupling
space への specialization は consumer 側に置く。独立した外部 package や `lean_lib`
target は作らず、workspace の `SYK` library の一部とする。

## 公開 API

中心となる公開結果は、standard Euclidean Gaussian measure 上の centered Lipschitz
function が Lipschitz constant の二乗を parameter とする `HasSubgaussianMGF` を持つことと
する。lower/upper/two-sided tail は mathlib の `HasSubgaussianMGF` API から導く。

smooth covariance estimate、Gaussian integration by parts、mollification、integrability
補題は内部 implementation とし、downstream が必要としない補助定義を公開しない。現在の
証明済み内容を弱い Poincare または Chebyshev bound に置き換えない。

## Module と namespace

files は `StandardGaussian.lean`、`Smooth.lean`、`Lipschitz.lean` とし、module path は
`SYK.Probability.GaussianConcentration.*`、declaration namespace は
`SYK.GaussianConcentration` とする。theorem、definition、file の命名は
`SYK/AGENTS.md` の mathlib naming 規則に従う。

## 検証

各 file を `lake env lean` で dependency order に検査する。公開 MGF theorem では
parameter が正確に `L^2` であることを確認し、主要 theorem の `#print axioms` を報告する。
`sorry`、`admit`、`axiom` または同等の未検証な仮定を導入しない。
