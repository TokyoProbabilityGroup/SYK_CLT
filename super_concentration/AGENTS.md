# AGENTS.md

## 適用範囲

このファイルは現在の `SYK/super_concentration/` 以下に適用する。再設計後は
`SYK/SuperConcentration/` へ移す。workspace ルート、`SYK/AGENTS.md`、共有模型の
`AGENTS.md` も適用する。

## 作業前に読む文書

1. `ARCHITECTURE.md`
2. `EDITING_PLAN.md`
3. `../SYK_model/ARCHITECTURE.md`
4. `../SYK_model/EDITING_PLAN.md`
5. `README.md`
6. 二つの blueprint（historical document としてのみ参照する）

正確な theorem と検証状態は Lean source、目標設計は `ARCHITECTURE.md`、作業順序は
`EDITING_PLAN.md` を優先する。

## 境界

有限座標型上の Gaussian measure、Herbst argument、mollification、Lipschitz Gaussian
concentration は `SYK/Probability/GaussianConcentration/` の独立 backend とする。この
backend に `N`、`q`、`InteractionIndex`、`CouplingSpace`、Majorana operator、Hamiltonianを
置かない。

`CouplingSpace` とその standard Gaussian measure は `SYKModel` に置く。この
directory には density-matrix estimate、Majorana sum-of-squares bound、physical
log-partition の Lipschitz estimate と concentration specialization だけを置く。

## 保護する数学的内容

- normalized trace による `Z(0)=1` と `log Z(0)=0`
- product standard Gaussian coupling law
- exact finite-volume Majorana sum-of-squares bound
- `β : ℝ≥0` に対する Gibbs-state derivative formula
- canonical scale における Lipschitz constant `β / sqrt q`
- centered log-partition の sub-Gaussian parameter `β^2 / q`
- lower/upper tail の先頭係数 `1`、two-sided tail の先頭係数 `2`
- exponent `-q t^2 / (2 β^2)`

`β=0` は constant function として扱う。complex temperature に positivity、density-matrix
性、real `log Z`、probability tail を一般化しない。一般 coupling scale `𝒥` は基本 APIに
含めず、必要なら coupling の scalar multiplicationから派生させる。

## Blueprint の状態

`blueprint_super_concentration.txt` の `N^(q/2)` scale と existential constant は、現行の
強い結果より弱い放棄済み target である。Gaussian blueprint の「upper-tail theorem に
唯一の `sorry` が残る」という記述と旧 path も現状と一致しない。これらを根拠に証明や
API を後退させない。

## 編集と検証

file/module component は再設計時に `UpperCamelCase` とする。互換 alias は作らない。
一度に dependency graph の一 layer だけを変更し、各変更ファイルを `lake env lean` で
検査する。最後に `lake build SYKModel SuperConcentration` と主要 theorem の
`#print axioms` を確認する。新しい placeholder は許容しない。
