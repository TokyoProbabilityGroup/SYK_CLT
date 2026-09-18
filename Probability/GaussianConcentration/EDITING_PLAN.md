# 汎用ガウス集中不等式の編集計画

## 担当範囲

この文書は、このディレクトリの `StandardGaussian.lean`、`Smooth.lean`、`Lipschitz.lean` の構成・証明・検証の細目を管理する。数学的規約と公開 API は [AGENTS.md](AGENTS.md) に従う。

全体の実行順序、状態、ファイル別の非同期実行の可否は [全体計画](../../EDITING_PLAN.md) を参照する。W02 はこの基盤だけでなく、Model の測度接続、SuperConcentration の利用側移行、Blueprint の更新を含む。ここでは他ディレクトリの編集を重複管理しない。

<a id="w02"></a>

## W02：独立した汎用基盤の構成

- [x] 旧ガウス集中モジュールの証明を再利用し、任意の有限型 `ι` に対する結果をこのディレクトリへ移す。名前空間を `SYK.GaussianConcentration` に統一し、利用側を import しない。
- [x] `StandardGaussian.lean` に有限次元ユークリッド空間の標準ガウス測度と必要な測度・可積分性の結果を置く。模型の `N`・`q`・`CouplingSpace` を持ち込まない。
- [x] `Smooth.lean` に滑らかな関数のガウス部分積分・共分散評価をまとめる。回転不変性、積分交換、勾配の計算の仮定を確認する。
- [x] `Lipschitz.lean` に平滑化と極限操作、Herbst の議論を使う公開 MGF・裾評価をまとめる。証明で必要な可積分性を明示し、`StandardGaussian.lean`・`Smooth.lean` の結果を使う。
- [x] 可積分性・型変換などの重複と不要な import を整理する。広範な証明探索に依存する既存部分は、数学的役割が明確な証明へ置き換える。
- [x] 中心化したリプシッツ関数の `HasSubgaussianMGF` をパラメータ `L^2` で供給する。`L=0` は定数関数として処理する。
- [x] 上側・下側・両側の裾評価を mathlib の `HasSubgaussianMGF` API から導き、分母に `L^2` を含む正の定数の公式と `L=0` を区別する。
- [x] 公開定理の型・名前・定数を確定し、Model と SuperConcentration の接続に必要な入力として示す。互換用の別名や SYK に限定した特殊化は基盤側に残さない。

担当部分の完了条件：3ファイルが依存順に検査され、定理文と推移的な import に SYK 固有のデータが現れず、正の `L` と `L=0` の結果が揃っている。独立した外部パッケージや `lean_lib` は作らない。移行元の整理は [SuperConcentration の W02](../../SuperConcentration/EDITING_PLAN.md#w02) が担当する。

## 検証と記録

各ファイルをワークスペースのルートから依存順に `lake env lean` で検査する。後続ファイルが import するモジュールは、次へ進む前に `lake build +<module>:olean` で成果物を生成する。3ファイルを検査した後に `lake build SYK` を実行する。公開 MGF のパラメータが正確に `L^2` であること、裾の定数、零の場合の処理、主要定理の `#print axioms` と残る仮定を確認する。新しい `sorry`、`admit`、`axiom` は許容しない。

対象コミット・差分、コマンド、結果、警告、未解決事項をこの節に記録する。W02 全体の完了には、接続後の `lake build Model SuperConcentration` と Blueprint の確認も必要であり、この担当部分の検査だけで全体計画を完了にしない。

2026-09-08 の文書再構成ではソースの配置と旧計画を照合しただけであり、この基盤の実装や Lean の再検証は行っていない。

### 2026-09-11：検証環境の判断待ち

対象は `e38b47ab56bc0d0aa7449452a8377ee67838a644`。着手時の作業ツリーは変更なし。関連する規約、W02 の各詳細計画、旧4ファイルの宣言と参照を調査した。既存の正の `L` の証明を任意の有限型のまま移設し、零の場合を追加する方針である。実装変更・ファイル移設・Lean の証明検査はまだ行っていない。

実際の親ディレクトリ `C:/Users/Public/Github/Lean` の `lakefile.lean` と `lake-manifest.json` は mathlib 4.32.1、`lean-toolchain` は Lean 4.32.1 を指定する。一方、このリポジトリの `workspace/` はコピー用テンプレートであり、Lean/mathlib 4.32.2 と VersoBlueprint を指定する。実際の親には VersoBlueprint、`Model`・`SuperConcentration` の個別ターゲット、`SYK.lean`・`SYKMain.lean` がない。他の研究ライブラリが登録されているため、テンプレートの上書きは行わない。テンプレートのディレクトリで `lake --version` を実行し、Lean 4.32.2 の実行可能性だけは確認した。これはソースや依存パッケージの検証ではない。

必要な判断は、他課題の設定を保持した共有環境の更新を許可するか、SYK 用の別ワークスペースと依存キャッシュの作成を許可するかである。後者なら共有環境の既存依存を更新せずに、テンプレートどおりの検証が可能になる。いずれも `workspace/AGENTS.md` の依存設定変更・別ワークスペース作成に関する規則により明示的な承認を必要とする。

再開地点：承認された方法で検証環境を整え、`StandardGaussian.lean` の測度・可積分性の抽出から開始する。各層の個別検査を通した後、Model・利用側・Blueprint を移行し、所定のビルド、公理依存、定数と仮定の照合を行う。過去の成功記録を今回の環境での成功として扱わない。

### 2026-09-11から2026-09-12：実装と統合検証

対象は `580792710437fb4b5c02c80aaaada0fee2acca85`。着手時の作業ツリーは変更なし。旧4ファイルを目標の3ファイルへ移し、名前空間を `SYK.GaussianConcentration` に変更した。汎用3ファイルの import と宣言には Model・SuperConcentration・`N`・`q`・`CouplingSpace` が現れない。公開 MGF 定理は `L ≥ 0` の下でパラメータ `Real.toNNReal (L^2)` を与え、正の `L` では上下・両側の裾を `exp (-t^2/(2L^2))` とその2倍で評価する。`L=0` では関数の定数性を証明し、MGF と上下・両側の空事象を別に処理した。

`StandardGaussian.lean`、`Smooth.lean`、`Lipschitz.lean` は依存順の `lake env lean` に成功し、各 `+SYK.Probability.GaussianConcentration.<module>:olean` も成功した。主要な測度、MGF、正の `L` の両側評価、零の場合の両側評価は `#print axioms` で `propext`、`Classical.choice`、`Quot.sound` のみに依存した。移設元由来の未使用 `simp` 引数、deprecated 名、`ring_nf` の提案などの warning は残る。新しい `sorry`、`admit`、`axiom` はない。

最初の `lake build SYK` は、親ワークスペースで `lakefile.lean` が `lakefile.toml` より優先され、既定範囲外の `Annealed_FE` と親環境にない Verso モジュールまで含めたため失敗した。承認後、親の `lakefile.lean` に `Model`、`SuperConcentration`、`CLT` の個別ターゲットと VersoBlueprint 4.32.0 を追加し、mathlib を4.32.2へ揃えた。`lake build Model SuperConcentration` は3194 jobs、`lake build SYK` は3553 jobsで成功した。汎用3層、`SYK.SuperConcentration.Main`、`SYK.Chapters.GaussianConcentration` の明示的な olean ターゲットも成功している。

Verso 4.32.0 は Windows 上で同梱検索資産の相対接頭辞を除けず、Blueprint 生成時に出力先の外を指すパスを作る。このため `BlueprintMain.lean` に Windows 限定の準備とコピーを追加した。所定の直接生成コマンドは成功し、`lake exe vbp check --site SYK/_out/site` は manifest と HTML cache が各52件、エラー0件で成功した。既存の未使用 `simp` 引数、deprecated 名、`ring_nf` の提案、Model の不足 docstring、VersoBlueprint の universe warning は残るが、W02 の未解決事項はない。
