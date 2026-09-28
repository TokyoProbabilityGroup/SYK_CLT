# AGENTS.md

## 適用範囲

このファイルは `SYK/Probability/GaussianConcentration/` 以下に適用する。ワークスペースのルートにある `AGENTS.md` と `SYK/AGENTS.md` の規則も適用する。このディレクトリは、SYK 模型から独立して、有限次元ユークリッド空間上のガウス集中不等式を提供する共通の基盤部分である。

## 作業計画

模型側・利用側への接続を含む全体の順序と状態は [全体計画](../../EDITING_PLAN.md) の指定 ID の行、このディレクトリの3ファイルの編集細目と現行の検証状態は [EDITING_PLAN.md](EDITING_PLAN.md) の該当節を確認する。完了済み作業の詳しい検証経緯は必要時に [作業履歴](../../WORK_HISTORY.md#gaussian-foundation) を参照する。

## 独立性

定理文とインポートによる依存関係に `ModelParameters`、`InteractionIndex`、`CouplingSpace`、`N`、`q`、マヨラナ演算子、ハミルトニアン、分配関数を導入しない。有限次元の結果は任意の有限型 `ι` に対して述べる。用途に応じて `ℝ`、座標空間 `ι → ℝ`、`EuclideanSpace ℝ ι` を使い、測度・ノルム・微分の対応を明示する。

この基盤部分は `Model`、`SuperConcentration`、`CLT` を `import` しない。SYK の相互作用係数の空間に適用するための定義や結果は、利用側に置く。独立した外部パッケージや `lean_lib` のビルド対象は作らず、ワークスペースの `SYK` ライブラリの一部とする。

## 公開 API

中心となる公開結果は、ユークリッド空間上の標準ガウス測度に関して中心化したリプシッツ関数が、リプシッツ定数の二乗をパラメータとする `HasSubgaussianMGF` を満たすこととする。下側・上側・両側の裾の評価は、mathlib の `HasSubgaussianMGF` API から導く。

モーメント母関数のパラメータの意味と `L = 0` の扱いは `SYK/SuperConcentration/ARCHITECTURE.md` の「共通ガウス集中不等式の定数」を参照する。

滑らかな関数の共分散評価、ガウス部分積分、平滑化、可積分性に関する補題は、利用側が実際に使うものだけを共有 API とし、不要な補助定義は公開しない。`gaussianReal_stein` などの既存宣言と重複させない。現在の証明済み内容を、それより弱いポアンカレ不等式やチェビシェフ不等式による評価に置き換えない。

## モジュールと名前空間

ファイル名は `StandardGaussian.lean`、`Smooth.lean`、`Lipschitz.lean` とし、モジュールのパスは `SYK.Probability.GaussianConcentration.*`、宣言を置く名前空間は `SYK.GaussianConcentration` とする。定理、定義、ファイルの命名は、`SYK/AGENTS.md` を通じて適用される mathlib に沿った命名規則に従う。

## 検証

各ファイルを依存先から順に `lake env lean` で検査し、後続ファイルが import するモジュールは次へ進む前に `lake build +<module>:olean` で成果物を生成する。担当部分の完了時には `lake build SYK` も実行する。公開するモーメント母関数（MGF）の定理では、パラメータが正確に `L^2` であることを確認し、主要な定理の `#print axioms` の結果を報告する。`sorry`、`admit`、`axiom` または同等の未検証な仮定を導入しない。
