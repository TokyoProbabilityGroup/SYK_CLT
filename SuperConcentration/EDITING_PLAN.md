# SYK 分配関数の対数に対する集中不等式の編集計画

## 管理範囲と現状

作業単位の選択・状態・待ち合わせは [全体計画](../EDITING_PLAN.md) で管理する。この文書は、このディレクトリ以下で行う W02 の旧配置整理と利用側移行、W03 の共有ハミルトニアンへの接続、W04 で必要な補題の移設元の修正、および W05 の集中評価の細目と検証根拠を記録する。移設先の証明と Blueprint の編集細目は、それぞれの担当ディレクトリの計画書に置く。

2026-09-08、コミット `05d64f4` のソースを確認した。ディレクトリと Lake のビルド対象の改名は完了している。`Core.lean` は共有の相互作用演算子・密度行列・Gibbs 解析を import しており、旧 `Gibbs.lean` は削除済み。`CouplingSpace` と標準ガウス測度も Model に移設済みである。これらを新規の実装課題として繰り返さない。

W02 で汎用ガウス集中は独立基盤へ移行済み。W03 で `Main.lean` のハミルトニアンを Model の共有定義へ接続し、微分・リプシッツ評価・両側の裾評価を標準規格化へ移行した。W05 では `Core.lean` を `DensityMatrix.lean`・`MajoranaBound.lean` に分割し、MGF・上下の裾を追加公開する。2026-09-08 の文書再編自体では Lean を再検証していない。

<a id="w02"></a>

## W02：汎用部分の旧配置整理と利用側移行

移設先の定義・証明・定数の検査は [汎用基盤の W02](../Probability/GaussianConcentration/EDITING_PLAN.md#w02)、模型の測度との接続は [Model の W02](../Model/EDITING_PLAN.md#w02) が管理する。ここでは移設元と直接の利用側を扱う。

- [x] `GaussianConcentration/` の `GaussianConcentrationAux.lean`、`GaussianCovSmooth.lean`、`GaussianCovMollify.lean`、`GaussianConcentration.lean` について、移設する宣言と残る参照を確認し、新基盤へ既存証明を引き渡す。
- [x] `N, q` への特殊化は、実際に必要なものだけを適用側に残す。模型の測度との同一性の結果は Model への移設後に旧定義を除き、不要な特殊化や互換用の別名を残さない。
- [x] 新基盤と Model の接続の検査後、`Main.lean` など、このディレクトリ内の直接の利用箇所の import・宣言参照を移行する。この単位では一般スケールを標準スケールに変更しない。
- [x] 移設済みの旧4ファイルを整理し、旧配置への参照が残っていないことを確認する。利用する汎用結果の正の `L` と `L=0` の条件を照合する。
- [x] 変更ファイルの個別検査と関連ビルドを行い、README・過去の証明計画書の旧パスと証明状態を更新する。過去の資料として残す記述は、その時点を明示する。

担当部分の完了条件：独立した汎用基盤を直接利用し、旧配置・重複定義・互換用の別名が残らず、既存の SYK 評価を維持している。W02 全体の完了には新基盤、Model、[Chapters](../Chapters/EDITING_PLAN.md) の担当部分と統合検証も必要である。

`Main.lean` の個別検査と `+SYK.SuperConcentration.Main:olean` は成功し、旧4モジュールへの Lean の参照は残っていない。README、構造文書、過去の証明計画書は新配置と履歴上の位置付けを明記するよう更新した。親ワークスペースへ個別ターゲットを追加した後、`lake build Model SuperConcentration` も成功した。2026-09-12には Blueprint の直接生成と参照検査も成功し、manifest と HTML cache は各52件、エラーは0件であった。詳細は汎用基盤の W02 検証記録を参照する。

<a id="w03"></a>

## W03：共有ハミルトニアンへの接続

[Model の W03](../Model/EDITING_PLAN.md#w03) で共有定義が確定してから、`Main.lean` の利用側を更新する。

- [x] `couplingScale`・`normalizedHamiltonian` とその基本性質の移設済み部分を除き、Model の標準スケールとハミルトニアンを使う。重複定義や互換用の別名を残さない。
- [x] 既存のアフィン性・自己共役性・対数微分・リプシッツ評価・裾評価を共有定義へ接続する。基本 API から一般スケール `𝒥` を分離し、標準ガウス座標 `g_A` に関する定数と零の場合を照合する。
- [x] `Main.lean` の個別検査、`lake build Model SuperConcentration`、変更した主要定理の公理依存の確認、およびこのディレクトリ内の対応文書の更新を行う。

担当部分の完了条件：共有ハミルトニアンを直接使い、既存の評価が標準規格化で検査されている。MGF・片側の裾の追加公開と集中評価の再配置は W05 に残す。

### 検証記録（2026-09-18）

着手時コミットは `475378724d3c2541711a15b19f3ec6500dbf8b2b`。Model の個別検査と olean 構築後に、移設元の重複定義を削除し、`Main.lean` の全 API から一般スケール `𝒥` とその符号仮定を除いた。有限サイズの二乗和評価、通常のトレースによる分配関数、方向微分の符号は保った。標準ガウス座標に関してリプシッツ定数は `β / sqrt q`、`β ≠ 0`・`t > 0` の両側の裾は `2 exp(-q t²/(2β²))` である。`β = 0` の `log Z = log card d` と裾の測度0も再検査した。`exactLipschitzSq` と `simpleLipschitzConstant` の配置・公開範囲の整理は W05 に残す。

- `lake env lean SYK/SuperConcentration/Main.lean` は warning なしで成功した。標準化により変わった平方根・二項係数の証明を調整し、未解決目標は残っていない。
- `lake build Model SuperConcentration` は3194 jobsで成功した。
- トレース商の方向微分、有限サイズの二乗評価、簡約された方向評価、熱期待値による方向微分、リプシッツ性、`β=0` の裾、公開両側の裾の `#print axioms` は `propext`、`Classical.choice`、`Quot.sound` のみであった。
- README・構造文書・過去の証明計画の位置付けを更新した。汎用基盤への SYK 依存や共有模型から集中評価への逆向き import、互換用の別名は追加していない。

`lake build` は3561 jobsで成功し、Blueprint の直接生成と `lake exe vbp check --site SYK/_out/site` も成功した。manifest と HTML cache は各63件、エラー0件であった。MGF と片側の裾の新しい模型固有定理はこの単位では追加していない。

<a id="w04"></a>

## W04：標準表現に必要な共有補題の移設元整理

[Model の W04](../Model/EDITING_PLAN.md#w04) で `Core.lean` の既存代数補題を必要とする場合だけ行う。標準表現そのものの証明をここで重複管理しない。

- [x] 必要な補題が Model に移設・検証された後、`Core.lean` の元の宣言を除き、利用箇所を共有宣言へ接続する。移設が不要なら、その確認を記録してこの担当部分を完了とする。
- [x] 移設した場合は変更ファイルと関連ビルドを検査し、二乗和評価の仮定と定数を保っていることを確認する。W05 の再配置との受け渡しは全体計画に従う。

担当部分の完了条件：標準表現が集中不等式側へ逆向きに依存せず、既存の集中評価も同じ共有補題を利用できる。

### W04 の検証記録（2026-09-18）

着手時コミットは `4a27dd8e77e99784683f460d2d5d826adac166e3`。`Core.lean` の `majorana_sq`、`listProduct_eq_smul_of_perm`、語の随伴との積、`psiProduct_star_mul_self`、`interactionOperator_sq` の証明を `Model.Majorana` へ移し、元の宣言を削除した。利用側は同じ共有宣言を直接使い、二乗和評価の仮定・有限サイズの定数は保った。

`lake env lean SYK/SuperConcentration/Core.lean` は warning なしで成功し、`lake build Model SuperConcentration` は3195 jobsで成功した。`syk_sum_sq_expectation_le` と `logPartition_two_sided_tail_standardGaussian` の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ。W05 のファイル再配置と MGF・片側評価の追加は未着手のまま残す。

<a id="w05"></a>

## W05：SYK 集中不等式の移行完了

前提は W01・W03（従って W02）。現行の二乗和評価は抽象的な `MajoranaSystem` に対する結果なので、W04 の標準表現の構成を待つ必要はない。

- [x] `Core.lean` の内容を目標配置の `DensityMatrix.lean` と `MajoranaBound.lean` に整理する。共有済みの密度行列の定義・Gibbs 解析は Model から使い、集中不等式固有の評価だけをこの層に残す。
- [x] 相互作用演算子の有限サイズの二乗和評価 `∑_A |Tr(ρ Ψ_A)|^2 ≤ choose(N,q-1)/q` を保持し、必要な代数補題の移設は W04 と競合しないよう調整する。
- [x] `β : ℝ≥0` と共有ハミルトニアンに対して既存の対数微分・方向微分の証明を再利用し、標準ガウス座標に関するリプシッツ定数 `β / sqrt q` を導く。
- [x] 中心化した対数分配関数に対し、パラメータ `β^2/q` の `HasSubgaussianMGF` を供給する。
- [x] 下側・上側・両側の裾評価を導く。`β>0`・`t>0` では片側が `exp(-q t^2/(2β^2))`、両側がその2倍となる定数を保持する。
- [x] `β=0` では通常のトレースによる `log Z=log d` が相互作用係数に依存しないことから、中心化した量が0となる場合を直接処理する。
- [x] 新 API の検証後、重複した定義、途中計算だけに使う公開定数、一般スケール `𝒥` を含む不要な旧基本 API を整理する。互換用の別名は作らない。
- [x] 個別検査、関連ビルド、主要定理の公理依存と定数の照合、README・過去の証明計画書の整合を完了する。

担当部分の完了条件：CLT が必要とする MGF と片側の裾を、定数を悪化させず、利用側が SYK のリプシッツ評価を仮定として補う必要のない形で供給できる。最良定数の同定は主張しない。対応する Blueprint の編集は Chapters の計画に従い、同じ W05 内で完了する。

### W05 の検証記録（2026-09-18）

着手時コミットは `9c8f0354a8429e7f943a34abd5415b1e8845c5dc`、着手時の作業ツリーに未コミットの変更はなかった。対象はそこからの W05 の未コミット差分であり、コミットは作成していない。

`Core.lean` の反交換族の評価を `DensityMatrix.lean`、拡張相互作用・二重計数・有限サイズ評価を `MajoranaBound.lean` に分割し、旧ファイルを削除した。両ファイルの証明本体が元の対応箇所と完全に一致することを比較した。密度行列の定義・分散の非負性・Gibbs 解析は Model の宣言を直接使い、有限サイズの上界は `choose(N,q-1)/q` のままである。

`Main.lean` の単一の公開定数は `logPartitionLipschitzConstant`。有限サイズの途中計算用定数とその補助定理を `private` にし、公開二乗評価には定数の式を直接記した。リプシッツ性を仮定として要求する旧両側裾の重複 API は削除し、互換用の別名は作っていない。

新しい `logPartition_hasSubgaussianMGF` は、中心化した通常トレースの対数分配関数に `Real.toNNReal (β²/q)` のパラメータを与え、`β=0` を含む。上下の裾はそれぞれ `exp(-q t²/(2β²))`、両側はその2倍であり、裾の表示は `β≠0`・`t>0` に限定する。零逆温度では `log Z=log card d`、中心化した量の点ごとの零、および上下・両側の正の偏差の測度0を直接証明した。模型固有のリプシッツ仮定を利用側に要求しない。

- 共有ワークスペースのルートで、最終ソースの `lake env lean SYK/SuperConcentration/DensityMatrix.lean`・`MajoranaBound.lean`・`Main.lean` はすべて warning なしで成功した。初回の `Main.lean` 検査は W03 より古い `GaussianDisorder` の olean により識別子不明で失敗したが、共有模型を再構築した後の検査は成功した。
- `lake build Model SuperConcentration` は3196 jobs、`lake build Model SuperConcentration CLT` は3202 jobsで成功した。汎用ガウス基盤の既存の linter warning は残り、変更した数学ファイルに新規 warning はない。親ワークスペースの既定対象は別研究の `RSATMain` なので、対象を明示して検証した。親の依存設定・既定対象は変更していない。
- 反交換族・有限サイズ二乗和・トレース商の方向微分・二乗方向評価・簡約方向評価・熱期待値の方向微分・リプシッツ性・MGF・零逆温度の中心化と上下両側の裾・正温度の上下両側の裾の計15定理を `#print axioms` で確認し、すべて `propext`・`Classical.choice`・`Quot.sound` のみであった。一時監査ファイルは削除した。
- Model・SuperConcentration・Probability・CLT の Lean ソースに `sorry`・`admit`・`axiom` は検出されず、旧 Core の import や旧公開定数・重複裾 API の利用箇所は残っていない。README・構造文書・歴史的証明計画の冒頭と Blueprint 原稿を更新し、`git diff --check` は成功した。
- `lake env lean SYK/Chapters/SuperConcentration.lean` は warning なしで成功した。Blueprint 原稿の宣言名・依存名もソースと照合した。Verso 休止中の生成・参照検査は実行していない。`Annealed_FE`・`Universality` は今回も検証していない。

## 各単位の検証と記録

変更ファイルを依存順に `lake env lean` で検査し、`lake build Model SuperConcentration` と主要定理の `#print axioms` を実行する。W02 の新基盤の個別検証は汎用基盤の計画に記録し、ここではその結果を受けて利用側からのビルドも確認する。ワークスペース全体に影響する変更では `lake build` を実行する。Blueprint の編集・検証と他の担当部分との統合は全体計画と Chapters の計画に従う。

パラメータ `L^2`・`β^2/q`、片側・両側の定数、零の場合の分岐と定理文に残る仮定を確認する。検証記録は対象コミット・差分、コマンド、結果、警告、公理依存を各単位の節に残す。ビルド成功だけで原稿との対応が済んだとしない。

`Annealed_FE` と `Universality` は既定ビルドから一時的に除外されており、その成功を両ライブラリの検証結果として扱わない。Verso 休止中は Blueprint の編集と宣言参照の照合を行い、生成・参照検査は復帰後にまとめて行う。既定範囲には新規エラーや新たな証明の未完成箇所を許容しない。

## 再編前の履歴

以下は旧段階0の棚卸し記録であり、宣言数・パス・対象ファイルは当時のものを指す。各単位の現在の完了状態や新しい検証結果ではない。

- [x] 現在の定理、依存する公理、ビルド結果、および利用箇所を記録する。
- [x] 証明計画書と Lean のソースコードについて、スケール、パス、証明状態の相違を記録する。
  - 棚卸し時点の対象は `Core.lean`、`Gibbs.lean`、`Main.lean`、旧ガウス集中不等式の4ファイルである。汎用部分には53宣言、共有模型・SYK 固有部分には83宣言がある。
  - 比較元は Git コミット `1b5a64cc9860f36876cc30b1a13d66ad4bfe8047` とする。旧版は Git 履歴で保持し、現行ファイルを直接改修する。旧 API を併存させる別モジュール、別名前空間、互換用の別名は作らない。
  - 定理文、規格化、数学的な証明の着想を保つ一方、証明スクリプトは重複の除去、mathlib の利用、可読性の改善のために置き換えてよい。変更後の定理文と定数は Lean の検査で確認する。

旧段階4のディレクトリ・ファイルの改名と Lake 対象の `SuperConcentration` への改名は完了済み。旧段階2の共有解析・相互作用演算子・係数空間の移設も完了済みである。残る標準ハミルトニアンは W03、集中評価の配置と公開 API の整理は W05 に対応する。

## 過去の証明計画書との相違

`blueprint_super_concentration.txt` にある `N^(q/2)` のスケールと、定数の存在のみを主張する評価は、現行の強い結果より弱い、放棄済みの目標である。ガウス集中不等式の証明計画書にある「上側の裾の定理に唯一の `sorry` が残る」という記述と旧パスも現状と一致しない。これらを根拠に証明や API を後退させない。
