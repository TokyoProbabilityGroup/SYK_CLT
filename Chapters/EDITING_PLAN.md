# Blueprint 各章の編集計画

## 担当範囲

この文書は、このディレクトリの `Model.lean`、`GaussianConcentration.lean`、`SuperConcentration.lean`、`AnnealedFE.lean`、`CLT.lean` に記す主要な主張と Lean 宣言の対応を管理する。全体の実行順序・状態・非同期実行の可否は [全体計画](../EDITING_PLAN.md)、守る条件は [SYK の作業規則](../AGENTS.md) の Blueprint の節を参照する。

各章の更新は対応する実装単位に含める。ここでは上流の数学的な証明を再実装せず、未実装の宣言を実装済みとして参照しない。本文は公開用の英語で記述する。

CLT の F01–F07 に対応する結果と固定した自己共役有限行列に対する Z01 の局所結果は実装済みである。F08 は仕様確定で完了した。`Annealed_FE` には未形式化部分が残る。統合担当が Lean コードを取り込み、個別検査・関連ビルド・主要宣言の公理依存と定理文の照合を終えた時点で、その実装済み範囲に限って章の証明状態・宣言参照・依存関係を編集する。Lean に残る外部仮定と `sorryAx` は内部証明と区別する。

## 現行の章と残件

`Model.lean`、`GaussianConcentration.lean`、`SuperConcentration.lean` は共有模型と集中評価の検証済み宣言を参照する。`Model.lean` は Z01 の局所非零円板と主値対数の正則性も参照する。`CLT.lean` は有限模型、ガウス–エルミート展開、高次剰余、および条件付きの共同・個別 CLT を参照する。三つの主 CLT は `0<|β|<β_q` に限定し、`AnnealedInput` の構築を内部証明として扱わない。`thm: input` の期待クエンチ・アニール圧力の決定論的極限と、Lean に導入済みのアニール入力を区別する。`AnnealedFE.lean` の未形式化部分は計画として明示する。

F01–F07 と Z01 の該当する章は、実装済み宣言への参照とソース上の照合を完了した。Z01 の局所円板は `N`・乱数標本に一様な領域と区別する。日付ごとの編集内容と検証結果は [作業履歴](../WORK_HISTORY.md#chapters-records)、[CLT の統合後検証](../WORK_HISTORY.md#clt-integration-audit-2026-09-29)、[Z01 の検証](../WORK_HISTORY.md#z01-local-zero-free-2026-09-28)を参照する。Verso による章検査・生成・参照検査は休止中である。

## 検証と記録

Verso 休止中は、変更した章の数学的主張・Lean 宣言名・依存名をソース上で照合する。Verso を必要とする章と生成入口の Lean 検査、生成、`vbp check` は復帰後に休止中の変更を含めて行う。章を並行して編集しても、統合検証の担当は一人とする。

新しい検証では対象コミット・差分、照合した宣言、コマンド、結果、警告、未解決の参照を記録する。過去の検証結果と旧コマンドは [作業履歴](../WORK_HISTORY.md#chapters-records) を参照する。
