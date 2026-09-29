# AGENTS.md

## 適用範囲

このファイルは `SYK/SuperConcentration/` 以下に適用する。ワークスペースのルート、`SYK/AGENTS.md`、共有模型の `AGENTS.md` の規則も適用する。

## 作業前に読む文書

1. `../EDITING_PLAN.md` の該当する残件
2. `EDITING_PLAN.md` の該当する残件
3. `ARCHITECTURE.md` と `../Model/ARCHITECTURE.md` の関係する規約・依存関係
4. 変更対象が Model の共有 API に及ぶ場合は `../Model/EDITING_PLAN.md` の該当する残件
5. 公開用の説明を変更する場合は `README.md`
6. 旧仕様との比較が必要な場合だけ二つの証明計画書

正確な定理文と検証状態は Lean のソースコード、現行設計は `ARCHITECTURE.md` を優先する。横断的な残件は `../EDITING_PLAN.md`、担当部分の残件は `EDITING_PLAN.md` を読む。完了済み作業の詳しい検証記録は必要になった場合だけ [作業履歴](../WORK_HISTORY.md) の該当節を読む。

汎用ガウス基盤を変更する場合は、`../Probability/GaussianConcentration/AGENTS.md` と同じ場所の `EDITING_PLAN.md` も読む。

## 役割の境界

有限の座標添字型に対するガウス測度、Herbst の議論、平滑化、リプシッツ関数に対するガウス集中不等式は、`SYK/Probability/GaussianConcentration/` の独立した基盤部分とする。この基盤部分に `N`、`q`、`InteractionIndex`、`CouplingSpace`、マヨラナ演算子、ハミルトニアンを置かない。

`CouplingSpace` とその標準ガウス測度は `Model` に置く。このディレクトリには、密度行列に関する評価、相互作用演算子 `Ψ_A` の期待値の絶対値の二乗和の評価、物理的な逆温度での分配関数の対数に対するリプシッツ評価、およびその集中不等式への適用だけを置く。

相互作用演算子と二乗和の定義は `ARCHITECTURE.md` の「SYK に固有の証明」を参照する。

## 保護する数学的内容

`ARCHITECTURE.md` の「SYK に固有の証明」に記録した規格化、座標、有限サイズの二乗和評価、ギブス状態の微分公式、モーメント母関数と裾の定数を保持する。最良定数の主張と、有効な上界を区別する。

`β=0` は定数関数として扱い、物理的な密度行列・実対数・裾確率の性質を複素逆温度へ一般化しない。一般スケール `𝒥` は基本 API に含めず、必要なら相互作用係数のスカラー倍から導く。

過去の証明計画書との相違は [作業履歴](../WORK_HISTORY.md#super-legacy) の該当節を必要な場合に確認し、旧記述を根拠に証明や API を後退させない。

## 編集と検証

一度に依存関係の一つの層だけを変更し、各変更ファイルを `lake env lean` で検査する。一つの指示が複数の層を含む場合も、層ごとの検証を通してから次の層へ進む。層の境界をユーザーの再承認や作業終了の境界とはしない。最後に `lake build Model SuperConcentration` と主要な定理の `#print axioms` を確認する。証明の未完成箇所を新たに導入することは許容しない。
