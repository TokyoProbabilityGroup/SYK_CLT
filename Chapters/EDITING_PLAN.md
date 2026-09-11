# Blueprint 各章の編集計画

## 担当範囲

この文書は、このディレクトリの `Model.lean`、`GaussianConcentration.lean`、`SuperConcentration.lean`、`CLT.lean` に記す主要な主張と Lean 宣言の対応を管理する。全体の実行順序・状態・非同期実行の可否は [全体計画](../EDITING_PLAN.md)、守る条件は [SYK の作業規則](../AGENTS.md) の Blueprint の節を参照する。

各章の更新は対応する実装単位に含める。ここでは上流の数学的な証明を再実装せず、未実装の宣言を実装済みとして参照しない。本文は公開用の英語で記述する。

## 各章の編集細目

- [x] W01：`Model.lean` に整関数性・複素微分・条件付き対数微分の主要宣言と依存関係を反映した。非零性の仮定を、零点のない領域の証明と混同していない。
- [x] SuperConcentration の移行前基準：`SuperConcentration.lean` に、一般スケール `𝒥` を含む現行実装の定義、二乗和評価、方向微分、勾配評価、Lipschitz 評価、逆温度が零の場合分け、両側集中不等式を記録した。主張の依存関係と証明だけで使う依存関係を分け、未実装の模型固有 MGF・片側評価を実装済みとして扱っていない。
- [x] W02：`GaussianConcentration.lean` の import と宣言参照を独立した汎用基盤へ切り替え、MGF・裾の定数と `L=0` の扱いを上流の定理に合わせる。
- [ ] W03：`Model.lean` と必要な `SuperConcentration.lean` の説明を共有の標準ハミルトニアンに合わせ、一般スケールを含む旧基本 API の参照を残さない。
- [ ] W04：`Model.lean` に標準表現・次元・基本関係・トレース直交性の主要宣言を反映する。抽象的な系の性質と具体的な表現の性質を区別する。
- [ ] W05：`SuperConcentration.lean` の参照と依存関係を新配置に合わせ、標準規格化の MGF・片側・両側の裾評価を公開宣言へ対応付ける。
- [ ] W06：`CLT.lean` に有限模型の規格化と共有結果との対応を反映する。有限模型の接続を最終 CLT の証明完了として表現しない。

F01–F08・Z01 の後続課題では、実装される主要宣言が確定した時点で対応する章の編集細目をここに追加する。現時点で仮の宣言参照は作らない。

## 検証と記録

変更した章をワークスペースのルートから `lake env lean` で個別に検査する。上流の変更が統合された後、`lake lean SYK/BlueprintMain.lean -- --run SYK/BlueprintMain.lean --output SYK/_out/site` と `lake exe vbp check --site SYK/_out/site` で生成と参照の整合性を確認する。章を並行して編集しても、統合検証の担当は一人とする。以下の過去の検証記録にある旧コマンドと出力先は当時のものであり、現在の手順とは区別する。

対象コミット・差分、コマンド、結果、警告、未解決の参照をこの節に記録する。`Annealed_FE` と `Universality` は既定ビルドから一時的に除外されているため、その成功を両ライブラリの検証結果として扱わない。既定範囲については Blueprint の生成と参照検査の成功を必要とする。

2026-09-08 の文書再構成では章の Lean ソースを編集しておらず、Blueprint の生成・参照検査も再実行していない。

W01 では `Model.lean` を個別に検査し、追加した3項目を含めて受理された。既存の `Params` と `MajoranaSystem` のフィールドにドキュメント文字列がないという warning は残る。`lake exe vbp build` は、編集対象外の `Annealed_FE` が旧 `Params.β`・`Params.β_nonneg` を参照する既知の2エラーで失敗した。生成物がないため `lake exe vbp check` も manifest 不在を報告した。いずれも成功とは記録しない。詳細は Model の W01 の検証記録を参照する。

SuperConcentration の移行前基準では、`lake env lean SYK/Chapters/SuperConcentration.lean` が warning なしで成功した。`lake exe vbp build` は `SYK.Chapters.SuperConcentration` と `SYK.Blueprint` の構築には成功したが、その後、編集対象外の `Annealed_FE/main_result.lean` に残る旧 `Params.β`・`Params.β_nonneg` 参照の2エラーで全体として失敗した。`lake exe vbp check` は生成されなかった manifest の不在を報告したため、全体の生成・参照検査は未完了である。

2026-09-08 に `Annealed_FE` と `Universality` を既定ビルドから一時除外した後、`lake exe vbp build` と `lake exe vbp check` は成功した。manifest と HTML cache は各50件で整合した。既存の宣言に対するドキュメント文字列の warning と VersoBlueprint の universe に関する warning は残る。

2026-09-11 の生成入口移設後の検証は、全体計画の「ビルド入口のプロジェクト内への移設」に記録する。章の本文・宣言参照は変更していない。

W02 では `GaussianConcentration.lean` の import と宣言参照を新しい名前空間へ切り替え、正の `L` の定数と零の場合の別定理を記録した。`SYK.Chapters.GaussianConcentration` の olean 構築と `lake build SYK` は成功した。2026-09-12、Windows で Verso 4.32.0 の同梱検索資産の相対接頭辞が残る問題に対し、`BlueprintMain.lean` に Windows 限定の準備とコピーを追加した。所定の直接生成コマンドは成功し、`lake exe vbp check --site SYK/_out/site` は manifest と HTML cache が各52件、エラー0件で成功した。既存の docstring と universe の warning は残る。
