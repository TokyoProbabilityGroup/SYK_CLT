# 汎用ガウス集中不等式の編集計画

## 現在の作業

W02 の汎用基盤の独立化と F01 のガウス–エルミート部分積分の共有配置は完了した。`StandardGaussian.lean`、`Smooth.lean`、`Lipschitz.lean` の現行 API と仮定は [AGENTS.md](AGENTS.md) と Lean ソースを参照する。移設・照合・検証の経緯は [ガウス基盤の履歴](../../WORK_HISTORY.md#gaussian-foundation) と [F01 の履歴](../../WORK_HISTORY.md#clt-f01-completion-2026-09-27) に保存した。SpinGlass の候補を調べた上で既存の SYK 側の補題を再利用した経緯も後者に記録した。

残る保守課題は、既存の局所証明における `aesop`・`grind` の使用を、対象と利用箇所を確認しながら整理することである。これは W02 の完了条件ではない。公開定理の仮定、`L²` の MGF パラメータ、`L=0` の扱いを変える場合は、利用側と定理文を照合し、変更ファイルを個別に検査して関連ビルド・公理依存を確認する。
