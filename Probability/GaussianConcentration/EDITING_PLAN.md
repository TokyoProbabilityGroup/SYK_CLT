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

W02 の完了状態は維持する。CLT 原稿の `lem:Gaussian-Hermite-IBP` に必要な模型から独立した部分を、既存の3ファイルの適切な層に追加する。SpinGlass の対象コミット・候補補題・Lean/mathlib の版差は [CLT の構造文書](../../CLT/ARCHITECTURE.md#依存関係と実装の分担)に集約する。対象補題の依存関係と移植後の互換性を検証し、上流の証明が存在するだけで移植先を証明済みとしない。着手順序は全体計画に従う。

- [ ] `StandardGaussian.lean` の `gaussianReal_stein` および `pi_gaussian_stein_coord` と、上流の定理文・仮定・規格化を比較し、一次元部分積分の実装を重複させない。分散1の標準ガウスを原稿の規格化と照合する。
- [ ] 必要な指数増大条件、積・和・多項式を掛けた場合の評価、ガウス可積分性を選択的に流用する。定義と証明を移植する場合は、出典・コミット・変更点・Apache 2.0 の表示をソースに残す。
- [ ] 高階の一次元部分積分と有限個の独立座標への反復に必要な汎用補題を定める。原稿のノルムによる評価から座標切片の指数増大を導き、切片の微分、測度の積と Fubini、積分される関数の可測性・可積分性を明示する。原稿が要求する `η ≤ α` の偏導関数だけで済むようにし、`pi_gaussian_stein_coord` の全座標勾配の仮定を反復時に暗黙に追加しない。

共有基盤の成果は、必要な正則性・成長条件を明示した汎用補題までとする。`Z_N` への特殊化は F04 の評価を受け取って CLT 側で行い、共有基盤の完了条件には含めない。エルミート展開の完全性・直交射影も [CLT の計画](../../CLT/EDITING_PLAN.md#formalization)で管理する。

完了条件：共有する宣言の定理文を原稿・既存 API・流用元と照合し、変更した Lean ファイルの個別検査、必要な最小ビルド、主要宣言の `#print axioms` を行う。公開 API が Model・CLT へ逆向きに依存しないことと、既存の集中評価を壊していないことを確認する。F01 全体の完了判定は [CLT の計画](../../CLT/EDITING_PLAN.md#formalization)に従う。

## 検証と記録

各ファイルをワークスペースのルートから依存順に `lake env lean` で検査する。後続ファイルが import するモジュールは、次へ進む前に `lake build +<module>:olean` で成果物を生成する。3ファイルを検査した後に `lake build SYK` を実行する。公開 MGF のパラメータが正確に `L^2` であること、裾の定数、零の場合の処理、主要定理の `#print axioms` と残る仮定を確認する。新しい `sorry`、`admit`、`axiom` は許容しない。

対象コミット・差分、コマンド、結果、警告、未解決事項をこの節に記録する。W02 全体には接続後の `lake build Model SuperConcentration` と Blueprint の編集・宣言参照の照合を含む。Verso 休止中は機械的な Blueprint 検証を要求しない。

2026-09-08 の文書再構成ではソースの配置と旧計画を照合しただけであり、この基盤の実装や Lean の再検証は行っていない。

2026-09-26：`pi_gaussian_stein_coord` の指数増大仮定を選択座標の偏導関数だけに弱めた。`StandardGaussian.lean` の個別 Lean 検査と、利用側 `Smooth.lean` のビルドに成功した。`CLT/GaussianIBP/GIBPMultiIndex.lean` ではユークリッドノルムの指数増大からこの補題への変換を検査した。`#print axioms` は共有の座標定理と CLT 側の変換定理について `[propext, Classical.choice, Quot.sound]` のみ。`lake build SYK` も成功したが、既存の `CLT/Main.lean` の `sorry` は残る。高階反復と `Z_N` への適用は未完了であり、F01 全体は未完了のまま。

### 2026-09-11：検証環境の判断待ち

対象は `e38b47ab56bc0d0aa7449452a8377ee67838a644`。着手時の作業ツリーは変更なし。関連する規約、W02 の各詳細計画、旧4ファイルの宣言と参照を調査した。既存の正の `L` の証明を任意の有限型のまま移設し、零の場合を追加する方針である。実装変更・ファイル移設・Lean の証明検査はまだ行っていない。

当時の共同研究者の親ワークスペースでは、`lakefile.lean` と `lake-manifest.json` が mathlib 4.32.1、`lean-toolchain` が Lean 4.32.1 を指定していた。一方、このリポジトリの `workspace/` はコピー用テンプレートであり、Lean/mathlib 4.32.2 と VersoBlueprint を指定していた。親ワークスペースには VersoBlueprint、`Model`・`SuperConcentration` の個別ターゲット、`SYK.lean`・`SYKMain.lean` がなかった。他の研究ライブラリが登録されていたため、テンプレートの上書きは行わなかった。テンプレートのディレクトリで `lake --version` を実行し、Lean 4.32.2 の実行可能性だけは確認した。これはソースや依存パッケージの検証ではない。

当時必要だった判断は、他課題の設定を保持した共有環境の更新を許可するか、SYK 用の別ワークスペースと依存キャッシュの作成を許可するかであった。いずれも依存設定変更・別ワークスペース作成に関する規則により明示的な承認を要した。

当時の再開地点：承認された方法で検証環境を整え、`StandardGaussian.lean` の測度・可積分性の抽出から開始する計画だった。この作業は次の「実装と統合検証」で完了している。

### 2026-09-11から2026-09-12：実装と統合検証

対象は `580792710437fb4b5c02c80aaaada0fee2acca85`。着手時の作業ツリーは変更なし。旧4ファイルを目標の3ファイルへ移し、名前空間を `SYK.GaussianConcentration` に変更した。汎用3ファイルの import と宣言には Model・SuperConcentration・`N`・`q`・`CouplingSpace` が現れない。公開 MGF 定理は `L ≥ 0` の下でパラメータ `Real.toNNReal (L^2)` を与え、正の `L` では上下・両側の裾を `exp (-t^2/(2L^2))` とその2倍で評価する。`L=0` では関数の定数性を証明し、MGF と上下・両側の空事象を別に処理した。

`StandardGaussian.lean`、`Smooth.lean`、`Lipschitz.lean` は依存順の `lake env lean` に成功し、各 `+SYK.Probability.GaussianConcentration.<module>:olean` も成功した。主要な測度、MGF、正の `L` の両側評価、零の場合の両側評価は `#print axioms` で `propext`、`Classical.choice`、`Quot.sound` のみに依存した。移設元由来の未使用 `simp` 引数、deprecated 名、`ring_nf` の提案などの warning は残る。新しい `sorry`、`admit`、`axiom` はない。

最初の `lake build SYK` は、親ワークスペースで `lakefile.lean` が `lakefile.toml` より優先され、既定範囲外の `Annealed_FE` と親環境にない Verso モジュールまで含めたため失敗した。承認後、親の `lakefile.lean` に `Model`、`SuperConcentration`、`CLT` の個別ターゲットと VersoBlueprint 4.32.0 を追加し、mathlib を4.32.2へ揃えた。`lake build Model SuperConcentration` は3194 jobs、`lake build SYK` は3553 jobsで成功した。汎用3層、`SYK.SuperConcentration.Main`、`SYK.Chapters.GaussianConcentration` の明示的な olean ターゲットも成功している。

Verso 4.32.0 は Windows 上で同梱検索資産の相対接頭辞を除けず、Blueprint 生成時に出力先の外を指すパスを作る。このため `BlueprintMain.lean` に Windows 限定の準備とコピーを追加した。所定の直接生成コマンドは成功し、`lake exe vbp check --site SYK/_out/site` は manifest と HTML cache が各52件、エラー0件で成功した。これは当時の Windows 共同研究環境の記録であり、現在の各ワークスペースへの設定適用を意味しない。既存の未使用 `simp` 引数、deprecated 名、`ring_nf` の提案、Model の不足 docstring、VersoBlueprint の universe warning は残る。`aesop`・`grind` を使う既存証明の整理は W02 後の保守課題である。
