# AGENTS.md

## 適用範囲と参照先

`SYK/Probability/GaussianConcentration/` 以下に適用する。このディレクトリは、SYK 模型から独立した共通の基盤として、有限次元ユークリッド空間上のガウス集中不等式を提供する。

環境構築と検証手順は [リポジトリのREADME](../../../README.md) を参照し、数学の検査はリポジトリ直下から実行する。

## 独立性と公開 API

定理文と `import` による依存に、`Params`、`InteractionIndex`、`CouplingSpace`、`N`、`q`、マヨラナ演算子、ハミルトニアン、分配関数を導入しない。有限次元の結果は任意の有限型 `ι` に対して述べる。用途に応じて `ℝ`、座標空間 `ι → ℝ`、`EuclideanSpace ℝ ι` を使い、測度・ノルム・微分の対応を明示する。

この基盤は `Model`、`SuperConcentration`、`CLT` を `import` しない。SYK の相互作用係数の空間に適用するための定義や結果は、利用側に置く。独立した外部パッケージや `lean_lib` のビルド対象は作らず、`SYK` パッケージの一部とする。

標準ガウスに対する公開 MGF のパラメータ `L^2` と `L = 0` の扱いを保つ。正確な型は [Lipschitz.lean](Lipschitz.lean)、SYK 模型での規格化と裾評価への適用は [SuperConcentrationのREADME](../../SuperConcentration/README.md) と [Main.lean](../../SuperConcentration/Main.lean) を参照する。

滑らかな関数の共分散評価、ガウス部分積分、平滑化、可積分性に関する補題は、利用側が実際に使うものだけを共有 API とし、不要な補助定義は公開しない。`gaussianReal_stein` などの既存宣言と重複させない。現在の証明済み内容を、それより弱いポアンカレ不等式やチェビシェフ不等式による評価に置き換えない。

## 依存と検証

モジュールは `SYK.Probability.GaussianConcentration.*`、宣言は名前空間 `SYK.GaussianConcentration` に置く。

Lean 実装の完了時には、公開 MGF の正確な型とパラメータを、上の `L^2`・`L = 0` の規約と利用側（SuperConcentration）に照合する。
