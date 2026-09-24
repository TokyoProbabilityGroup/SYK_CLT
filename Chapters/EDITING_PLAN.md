# Blueprint 各章の編集計画

## 担当範囲

この文書は、このディレクトリの `Model.lean`、`GaussianConcentration.lean`、`SuperConcentration.lean`、`CLT.lean` に記す主要な主張と Lean 宣言の対応を管理する。全体の実行順序・状態・非同期実行の可否は [全体計画](../EDITING_PLAN.md)、守る条件は [SYK の作業規則](../AGENTS.md) の Blueprint の節を参照する。

各章の更新は対応する実装単位に含める。ここでは上流の数学的な証明を再実装せず、未実装の宣言を実装済みとして参照しない。本文は公開用の英語で記述する。

## 各章の編集細目

- [x] W01：`Model.lean` に整関数性・複素微分・条件付き対数微分の主要宣言と依存関係を反映した。非零性の仮定を、零点のない領域の証明と混同していない。
- [x] SuperConcentration の移行前基準：`SuperConcentration.lean` に、一般スケール `𝒥` を含む現行実装の定義、二乗和評価、方向微分、勾配評価、Lipschitz 評価、逆温度が零の場合分け、両側集中不等式を記録した。主張の依存関係と証明だけで使う依存関係を分け、未実装の模型固有 MGF・片側評価を実装済みとして扱っていない。
- [x] W02：`GaussianConcentration.lean` の import と宣言参照を独立した汎用基盤へ切り替え、MGF・裾の定数と `L=0` の扱いを上流の定理に合わせる。
- [x] W03：`Model.lean` と必要な `SuperConcentration.lean` の説明を共有の標準ハミルトニアンに合わせ、一般スケールを含む旧基本 API の参照を残さない。
- [x] W04：`Model.lean` に標準表現・次元・基本関係・トレース直交性の主要宣言を反映する。抽象的な系の性質と具体的な表現の性質を区別する。
- [x] W05：`SuperConcentration.lean` の参照と依存関係を新配置に合わせ、標準規格化の MGF・片側・両側の裾評価を公開宣言へ対応付ける。
- [ ] W06：`CLT.lean` に有限模型の規格化と共有結果との対応を反映する。有限模型の接続を最終 CLT の証明完了として表現しない。

F01–F08・Z01 の後続課題では、実装される主要宣言が確定した時点で対応する章の編集細目をここに追加する。現時点で仮の宣言参照は作らない。

## 検証と記録

Verso 休止中は、変更した章の数学的主張・Lean 宣言名・依存名をソース上で照合する。Verso を必要とする `lake env lean`、生成入口の実行、`vbp check` は復帰後に休止中の変更を含めてまとめて行う。章を並行して編集しても、統合検証の担当は一人とする。以下の過去の検証記録にある旧コマンドと出力先は当時のものであり、現在の手順とは区別する。

2026-09-18：明示的に `sorry` を許可された `CLT/Main.lean` の定理文追加に合わせ、`CLT.lean` に一般の非空有限次元 Majorana 表現・次元による規格化・アニール極限・両 CLT の式と共同半径・非零逆温度での標準化条件を記した。Lean 宣言への対応を付け、未証明状態を明示した。W06・F06・F07 の完了記録ではない。Verso の生成・参照検査は休止中のため行わない。関連検証は [CLT の記録](../CLT/EDITING_PLAN.md#main-statements-2026-09-18) に集約する。


対象コミット・差分、照合した宣言、コマンド、結果、警告、未解決の参照をこの節に記録する。`Annealed_FE` と `Universality` は既定ビルドから一時的に除外されているため、その成功を両ライブラリの検証結果として扱わない。Verso 復帰後は Blueprint の生成と参照検査を行う。

2026-09-08 の文書再構成では章の Lean ソースを編集しておらず、Blueprint の生成・参照検査も再実行していない。

W01 では `Model.lean` を個別に検査し、追加した3項目を含めて受理された。既存の `Params` と `MajoranaSystem` のフィールドにドキュメント文字列がないという warning は残る。`lake exe vbp build` は、編集対象外の `Annealed_FE` が旧 `Params.β`・`Params.β_nonneg` を参照する既知の2エラーで失敗した。生成物がないため `lake exe vbp check` も manifest 不在を報告した。いずれも成功とは記録しない。詳細は Model の W01 の検証記録を参照する。

SuperConcentration の移行前基準では、`lake env lean SYK/Chapters/SuperConcentration.lean` が warning なしで成功した。`lake exe vbp build` は `SYK.Chapters.SuperConcentration` と `SYK.Blueprint` の構築には成功したが、その後、編集対象外の `Annealed_FE/main_result.lean` に残る旧 `Params.β`・`Params.β_nonneg` 参照の2エラーで全体として失敗した。`lake exe vbp check` は生成されなかった manifest の不在を報告したため、全体の生成・参照検査は未完了である。

2026-09-08 に `Annealed_FE` と `Universality` を既定ビルドから一時除外した後、`lake exe vbp build` と `lake exe vbp check` は成功した。manifest と HTML cache は各50件で整合した。既存の宣言に対するドキュメント文字列の warning と VersoBlueprint の universe に関する warning は残る。

2026-09-11 の生成入口移設後の検証は、全体計画の「ビルド入口のプロジェクト内への移設」に記録する。章の本文・宣言参照は変更していない。

W02 では `GaussianConcentration.lean` の import と宣言参照を新しい名前空間へ切り替え、正の `L` の定数と零の場合の別定理を記録した。`SYK.Chapters.GaussianConcentration` の olean 構築と `lake build SYK` は成功した。2026-09-12、Windows で Verso 4.32.0 の同梱検索資産の相対接頭辞が残る問題に対し、`BlueprintMain.lean` に Windows 限定の準備とコピーを追加した。所定の直接生成コマンドは成功し、`lake exe vbp check --site SYK/_out/site` は manifest と HTML cache が各52件、エラー0件で成功した。既存の docstring と universe の warning は残る。

### W03 の検証記録（2026-09-18）

対象は着手時コミット `475378724d3c2541711a15b19f3ec6500dbf8b2b` からの未コミット差分。標準スケール・ハミルトニアンの定義ノードを同じ ID のまま Model 章へ移し、スケールの二乗・実線形性・自己共役性の宣言を追加した。各実係数の分散と標準座標 `g_A` を区別し、講義ノートの `eq:Hqnormalized`・`eq:Jcovariance` と CLT 原稿の `subsec:SYK-model` との対応を記した。集中評価の章では一般スケールの引数・仮定を除き、方向微分、有限サイズ評価、リプシッツ定数 `β / sqrt q`、`β = 0` と両側の裾 `2 exp(-q t²/(2β²))` を現在の宣言に合わせた。MGF・片側の裾の模型固有定理は未公開のまま区別した。

- 初回の `lake env lean SYK/Chapters/Model.lean` はこのワークスペースの Verso olean が未構築のため失敗した。その後 `lake build` で既存依存を構築し、再検査した。
- `lake build` は3561 jobsで成功した。`Annealed_FE` と `Universality` は既定対象から除外されたままであり、この結果は両ライブラリの検証ではない。
- `lake env lean SYK/Chapters/Model.lean` と `lake env lean SYK/Chapters/SuperConcentration.lean` は成功した。Model 章には既存の `Params`・`MajoranaSystem` のフィールドの docstring warning が残り、SuperConcentration 章に warning はなかった。
- `lake lean SYK/BlueprintMain.lean -- --run SYK/BlueprintMain.lean --output SYK/_out/site` は成功した。
- `lake exe vbp check --site SYK/_out/site` は初回の検査用実行ファイルの構築後に成功した。manifest と HTML cache は各63件、エラー0件であった。生成済み HTML に Model 章の標準ハミルトニアン定義・基本性質・Lean 宣言リンクがあることも確認した。新たな未解決参照はない。

### W04 の検証記録（2026-09-18）

対象は着手時コミット `4a27dd8e77e99784683f460d2d5d826adac166e3` からの未コミット差分。Model 章に標準表現・次元・生成子の基本関係・共有相互作用の自己共役性と二乗・規格化トレース直交性の5項目を追加した。Jordan–Wigner の Pauli Y の符号、テンソルの順序、0始まりの添字と講義ノートの1始まりの添字の対応を明記し、講義ノートの `eq:majoranaCAR` と CLT 原稿の `subsec:SYK-model` との対応を記した。同じ偶数次数の直交性は構成済みの標準表現に対する結論として記し、抽象構造への追加仮定や異なる次数を混ぜた族の主張は置いていない。

- `lake env lean SYK/Chapters/Model.lean` は成功した。既存の `Params`・`MajoranaSystem` のフィールドの docstring warning は残る。
- `lake build` は3562 jobsで成功した。既存のガウス基盤などの linter warning と VersoBlueprint の universe warning は残る。`Annealed_FE` と `Universality` は既定対象から除外されたままで、今回も検証していない。
- `lake lean SYK/BlueprintMain.lean -- --run SYK/BlueprintMain.lean --output SYK/_out/site` は成功した。
- `lake exe vbp check --site SYK/_out/site` は manifest と HTML cache が各89件、エラー0件で成功した。生成済みの Model 章 HTML に追加した5項目と標準表現・直交性の Lean 宣言リンクがあることを確認した。未解決参照はない。

### W05 の検証記録（2026-09-18）

対象は着手時コミット `9c8f0354a8429e7f943a34abd5415b1e8845c5dc` からの未コミット差分。SuperConcentration 章の配置説明を `DensityMatrix`・`MajoranaBound`・`Main` に合わせ、MGF と上下の裾の2項目を追加し、零逆温度の点ごとの中心化を公開宣言に対応付けた。MGF パラメータ `β²/q`、片側の指数 `-q t²/(2β²)`、両側の係数2、通常トレース・標準ガウス座標・非空の有限行列表現・逆温度の範囲は Lean の定理文と照合した。最良定数や分散の等式は主張していない。

`lake env lean SYK/Chapters/SuperConcentration.lean` は warning なしで成功した。宣言名と依存名を保存された章・数学ソースで照合し、未定義名は検出されなかった。上流の `lake build Model SuperConcentration CLT` と主要15定理の公理依存確認も成功した。Verso の休止に従い、HTML の生成・参照検査は実行しておらず、その成功は主張しない。
