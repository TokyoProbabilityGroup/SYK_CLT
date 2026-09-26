# 汎用ガウス集中不等式の編集計画

## 担当範囲

この文書は、このディレクトリの `StandardGaussian.lean`、`Smooth.lean`、`Lipschitz.lean` の構成・証明・検証の細目を管理する。F01 で共有するガウス解析もここで管理する。数学的規約と公開 API は [AGENTS.md](AGENTS.md) に従う。

全体の実行順序、状態、ファイル別の非同期実行の可否は [全体計画](../../EDITING_PLAN.md) を参照する。W02 はこの基盤だけでなく、Model の測度接続、SuperConcentration の利用側移行、Blueprint の更新を含む。ここでは他ディレクトリの編集を重複管理しない。

<a id="w02"></a>

## W02：独立した汎用基盤の構成

- [x] 旧ガウス集中モジュールの証明を再利用し、任意の有限型 `ι` に対する結果をこのディレクトリへ移す。名前空間を `SYK.GaussianConcentration` に統一し、利用側を import しない。
- [x] `StandardGaussian.lean` に有限次元ユークリッド空間の標準ガウス測度と必要な測度・可積分性の結果を置く。模型の `N`・`q`・`CouplingSpace` を持ち込まない。
- [x] `Smooth.lean` に滑らかな関数のガウス部分積分・共分散評価をまとめる。回転不変性、積分交換、勾配の計算の仮定を確認する。
- [x] `Lipschitz.lean` に平滑化と極限操作、Herbst の議論を使う公開 MGF・裾評価をまとめる。証明で必要な可積分性を明示し、`StandardGaussian.lean`・`Smooth.lean` の結果を使う。
- [x] 可積分性・型変換などの重複と不要な import を整理した。`aesop`・`grind` を使う既存の局所証明は残っており、これは W02 の公開 API・統合検証とは別の保守課題として記録する。
- [x] 中心化したリプシッツ関数の `HasSubgaussianMGF` をパラメータ `L^2` で供給する。`L=0` は定数関数として処理する。
- [x] 上側・下側・両側の裾評価を mathlib の `HasSubgaussianMGF` API から導き、分母に `L^2` を含む正の定数の公式と `L=0` を区別する。
- [x] 公開定理の型・名前・定数を確定し、Model と SuperConcentration の接続に必要な入力として示す。互換用の別名や SYK に限定した特殊化は基盤側に残さない。

担当部分の完了条件：3ファイルが依存順に検査され、定理文と推移的な import に SYK 固有のデータが現れず、正の `L` と `L=0` の結果が揃っている。独立した外部パッケージや `lean_lib` は作らない。移行元の整理は [SuperConcentration の W02](../../SuperConcentration/EDITING_PLAN.md#w02) が担当する。

<a id="f01"></a>

## F01：ガウス部分積分の共有基盤

W02 の完了状態は維持する。以下は共有配置・既存 API との整理に関する計画であり、一般 Hermite 部分積分を未証明として再実装する指示ではない。2026-09-26、`pi_gaussian_stein_coord` の選択座標化と、`CLT/Lemmas/GaussianIBP.lean` の一般部分積分・両辺の可積分性は検証済みである。高階の汎用部分が CLT 側にある現状は共有層への配置方針と一致しておらず、出典・重複・配置の整理が残る。検証根拠は [ガウス部分積分の記録](../../WORK_HISTORY.md#clt-f01-gaussian) と [統合監査](../../WORK_HISTORY.md#clt-w06) を参照する。

CLT 原稿の `lem:Gaussian-Hermite-IBP` に必要な模型から独立した部分を、既存の3ファイルの適切な層に追加する。SpinGlass の対象コミット・候補補題・Lean/mathlib の版差は [CLT の構造文書](../../CLT/ARCHITECTURE.md#依存関係と実装の分担)に集約する。対象補題の依存関係と移植後の互換性を検証し、上流の証明が存在するだけで移植先を証明済みとしない。着手順序は全体計画に従う。

- [ ] `StandardGaussian.lean` の `gaussianReal_stein` および `pi_gaussian_stein_coord` と、上流の定理文・仮定・規格化を比較し、一次元部分積分の実装を重複させない。分散1の標準ガウスを原稿の規格化と照合する。
- [ ] 必要な指数増大条件、積・和・多項式を掛けた場合の評価、ガウス可積分性を選択的に流用する。定義と証明を移植する場合は、出典・コミット・変更点・Apache 2.0 の表示をソースに残す。
- [ ] 検証済みの `CLT/Lemmas/GaussianIBP.lean` にある高階の一次元部分積分と有限個の独立座標への反復を調べ、共有する補題と配置を確定する。原稿のノルムによる評価から座標切片の指数増大を導き、切片の微分、測度の積と Fubini、積分される関数の可測性・可積分性を明示する。原稿が要求する `η ≤ α` の偏導関数だけで済むようにし、旧 `pi_gaussian_stein_coord` にあった全座標勾配の成長仮定を再導入しない。

共有基盤の成果は、必要な正則性・成長条件を明示した汎用補題までとする。`Z_N` への特殊化は F04 の評価を受け取って CLT 側で行い、共有基盤の完了条件には含めない。エルミート展開の完全性・直交射影も [CLT の計画](../../CLT/EDITING_PLAN.md#formalization)で管理する。

後続の F01-G では、`CLT/Lemmas/GaussianIBP.lean` の公開宣言と全参照を調べてから汎用部分を共有配置へ移す。旧 `IBPFamily` などの補助構造は、利用先がないことを確認してから整理する。局所的な抽出検査だけを根拠に大きな証明部分を削除しない。担当範囲と受け渡し条件は [F01-G](../../CLT/EDITING_PLAN.md#ticket-f01-g) に置く。

完了条件：共有する宣言の定理文を原稿・既存 API・流用元と照合し、変更した Lean ファイルの個別検査、必要な最小ビルド、主要宣言の `#print axioms` を行う。公開 API が Model・CLT へ逆向きに依存しないことと、既存の集中評価を壊していないことを確認する。F01 全体の完了判定は [CLT の計画](../../CLT/EDITING_PLAN.md#formalization)に従う。

## 検証と記録

各ファイルをワークスペースのルートから依存順に `lake env lean` で検査する。後続ファイルが import するモジュールは、次へ進む前に `lake build +<module>:olean` で成果物を生成する。3ファイルを検査した後に `lake build SYK` を実行する。公開 MGF のパラメータが正確に `L^2` であること、裾の定数、零の場合の処理、主要定理の `#print axioms` と残る仮定を確認する。新しい `sorry`、`admit`、`axiom` は許容しない。

対象コミット・差分、コマンド、結果、警告、未解決事項を検査時に記録し、現行の結論と残作業を該当節へ反映する。詳しい完了記録は [作業履歴](../../WORK_HISTORY.md#gaussian-foundation) に置く。W02 全体には接続後の `lake build Model SuperConcentration` と Blueprint の編集・宣言参照の照合を含む。Verso 休止中は機械的な Blueprint 検証を要求しない。

過去の移設・検証経緯は [作業履歴](../../WORK_HISTORY.md#gaussian-foundation) に保存した。
