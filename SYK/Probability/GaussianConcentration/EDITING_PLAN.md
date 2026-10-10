# 汎用ガウス集中不等式の保守課題

探索タクティク（`aesop`・`grind`）と非推奨 API は整理済みである。`maxHeartbeats` の引き上げは、`gaussianReal_stein` の1か所（既定値の2倍）だけが残る。残る課題は、linter の警告431件（`StandardGaussian` 257件、`Smooth` 174件。`Lipschitz` は解消済み）の解消である。種類と解決方法は [全体計画の `MAINT-LINT`](../../../EDITING_PLAN.md#maint-lintlinter-の警告) に記す。独立した保守作業として扱い、状態と担当は [全体計画](../../../EDITING_PLAN.md#残る作業) に集約する。

公開定理の型、仮定、結論と、MGF のパラメータ `L²` と `L=0` の扱いを保つ。模型や CLT の入力を汎用の基盤に導入せず、逆向きの import も作らない。現行の API と定数は、[構造説明](../../SuperConcentration/ARCHITECTURE.md#汎用的な基盤部分の分離) と Lean ソースで確認する。

完了条件は次のとおりである。

- 対象の警告を解消する。未使用のインスタンス引数（8件）を外すと定理文の仮定が変わるので、承認を得てから行う。
- 変更したファイルと直接の利用側を個別に検査し、関連するビルドと `lake build SYK` を実行する。
- 主要定理の型と公理依存を照合する。

残した警告は、その理由とともに報告する。過去の独立化と部分積分の共有化は、[作業履歴](../../../WORK_HISTORY.md#gaussian-foundation) に記す。
