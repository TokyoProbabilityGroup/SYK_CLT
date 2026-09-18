# 共有 SYK 模型の編集計画

## 管理範囲と現状

実行する単位とその状態は [全体計画](../EDITING_PLAN.md) で管理する。この文書は Model 内のファイル群について、W01・W02 の測度接続・W03・W04・Z01 の細目と検証根拠を記録する。利用側や Blueprint の編集細目は、その担当ディレクトリの計画書に置く。作業単位内のチェック項目は、個別の承認やコミットの区切りではない。

2026-09-08、コミット `05d64f4` の配置・宣言を確認した。以下の「実装あり」は、文書再編で新たに Lean を実行したという意味ではない。検証の履歴は末尾に残す。

| 内容 | 現状と残作業 |
| --- | --- |
| パラメータ・共有代数 | 逆温度の分離、相互作用添字、昇順積、位相、相互作用演算子、確定的ハミルトニアンは移行済み |
| 有限次元の解析・物理量 | 通常の分配関数、`normalizedTrace`、物理的 Gibbs API、実方向微分、整関数性・複素微分・条件付き対数微分は実装・検証済み。零点のない領域は Z01 |
| ガウス型相互作用 | `CouplingSpace`・`couplingSpace_card`・`standardGaussianMeasure` は Model に移設済み。汎用測度との接続は W02、標準スケールとハミルトニアンは W03 で共有化 |
| 標準表現 | W04 で Jordan–Wigner 表現と同じ偶数次数の相互作用の直交性を構成・検証済み。抽象的な `MajoranaSystem` の仮定は追加していない |
| 利用側 | 集中不等式の移行完了は W05、CLT 固有の規格化分配関数と接続は W06 |

<a id="w01"></a>

## W01：共有行列解析の仕上げ

`partitionFunction_has_deriv_at`、`partitionFunction_differentiable`、`partitionFunction_analytic_at`、`partitionFunction_mul_log_deriv` は追加済みである。これらを二つの実装課題に分け直さず、残る確認・記録を一単位で完了する。

- [x] 追加済みの定理の型・仮定・符号と通常のトレース規約を照合した。`logDeriv` の商の公式を、複素対数の枝や零点のない領域の構成と混同していない。
- [x] `FiniteDimensionalGibbs.lean` を個別に検査し、`lake build Model SuperConcentration` と追加した主要定理の `#print axioms` を確認した。
- [x] 差分、警告、既知の失敗と今回の検証範囲を記録し、構造文書と Blueprint の現在の状態を更新した。

担当部分の完了条件：追加の解析 API と Model 内の対応文書が一致し、上記の検証結果が記録されている。W01 全体では [Chapters の計画](../Chapters/EDITING_PLAN.md) に記す章の更新と宣言参照の照合も含む。Verso の機械的検証は休止中は要求しない。CLT の局所定義や零点のない領域の証明は含めない。

### 検証記録（2026-09-08）

対象実装はコミット `05d64f4` の `FiniteDimensionalGibbs.lean` に追加された4定理である。通常のトレースによる `Z_H(z) = Tr(exp(-zH))` について、複素微分は `Z_H'(z) = -Tr(H * exp(-zH))`、解析性は各 `z : ℂ` での `AnalyticAt`、対数微分の公式は `Z_H(z) ≠ 0` を仮定する点ごとの商公式であることを照合した。自己共役性、実逆温度、零点のない領域、複素対数の枝はこの4定理の仮定・結論に含まれない。

- `lake env lean SYK/Model/FiniteDimensionalGibbs.lean` は成功した。
- `lake build Model SuperConcentration` は3195 jobsで成功した。今回の対象ファイルには、既存の `density_variance_nonneg` の型にある未使用の `[DecidableEq d]` に関する linter warning が残る。`SuperConcentration/GaussianConcentration/` の既存の `refine'`・柔軟な `simp`・長い行などの warning と `Main.lean` の copyright header warning も残るが、W01 は変更していない。
- `#print axioms` で `partitionFunction_has_deriv_at`、`partitionFunction_differentiable`、`partitionFunction_analytic_at`、`partitionFunction_mul_log_deriv` を確認した。いずれも `propext`、`Classical.choice`、`Quot.sound` のみへ依存し、`sorry`、`admit`、追加の `axiom` は示されなかった。

Blueprint の章は W01 の3項目を追加して `lake env lean SYK/Chapters/Model.lean` で個別に検査し、受理された。既存の `Params` と `MajoranaSystem` のフィールドにドキュメント文字列がないという warning は残る。`lake exe vbp build` は編集対象外の `Annealed_FE/main_result.lean` が廃止済みの `Params.β`・`Params.β_nonneg` を参照する既知の2エラーで失敗した。Blueprint の章と `SYK.Blueprint` はその前にビルドされたが、生成物は完成していない。続く `lake exe vbp check` は manifest 不在を報告した。いずれも成功とは記録しない。

<a id="w02"></a>

## W02：汎用ガウス測度への接続

新基盤の測度が確定した後、`GaussianDisorder.lean` の模型側の定義を接続する。受け渡しの順序は全体計画に従う。

- [x] `standardGaussianMeasure` を、[汎用基盤](../Probability/GaussianConcentration/EDITING_PLAN.md#w02) の有限型に対する測度を使う定義に揃え、積測度を重複定義しない。`CouplingSpace` とその次元の定義は再利用する。
- [x] 模型の測度と汎用測度の一致を利用側で扱えることを確認する。同一性の既存結果を移す場合は Model 側に置き、汎用側が Model を import する依存を除く。
- [x] `GaussianDisorder.lean` の個別検査と Model のビルドを行い、定義・必要な測度の性質と import を確認する。

担当部分の完了条件：Model が独立した汎用測度を利用し、通常の標準ガウス座標の規約を維持している。利用側の import 切替は [SuperConcentration の W02](../SuperConcentration/EDITING_PLAN.md#w02) で管理する。

`GaussianDisorder.lean` の個別検査と `+SYK.Model.GaussianDisorder:olean` は成功した。`standardGaussianMeasure_eq_onEuclidean` の公理依存は `propext`、`Classical.choice`、`Quot.sound` のみである。親ワークスペースの `lakefile.lean` に `Model`、`SuperConcentration`、`CLT` の個別ターゲットを追加した後、`lake build Model SuperConcentration` は3194 jobsで成功した。2026-09-12には Blueprint の直接生成と参照検査も成功し、manifest と HTML cache は各52件、エラーは0件であった。

<a id="w03"></a>

## W03：ガウス型 SYK ハミルトニアンの共有化

前提は W02。測度の独立化と利用側の import 移行が終わった後に、同じ利用側ファイルの規格化を移行する。

- [x] 移設済みの `CouplingSpace` と標準ガウス測度を再利用し、`σ_N² = (q-1)! / N^(q-1)` に対応する標準スケールを `Model.GaussianDisorder` に置く。
- [x] 標準規格化ハミルトニアンを共有する確定的ハミルトニアンから定義し、線形性・自己共役性など利用側で必要な既存の結果を移す。
- [x] Model の基本 API は標準スケールに限定し、一般スケール `𝒥` や互換用の別名を重複して公開しない。移行元の削除と微分・リプシッツ・裾評価の追従は [SuperConcentration の W03](../SuperConcentration/EDITING_PLAN.md#w03) で管理する。
- [x] 個別検査、Model と移行済み利用側のビルド、主要定理の公理依存、このディレクトリ内の対応文書の更新を完了する。

担当部分の完了条件：標準の相互作用係数とハミルトニアンが Model の一つの定義系列になる。W03 全体は直接の利用側への移行と統合検証まで含めて完了する。各係数の分散と、ガウス座標 `g_A` に関する評価であることを明記する。

### 検証記録（2026-09-18）

対象は着手時コミット `475378724d3c2541711a15b19f3ec6500dbf8b2b` からの未コミット差分。着手時の SYK 作業ツリーは変更なし。`couplingScale P` と `normalizedHamiltonian P M g`、アフィン性・自己共役性を `GaussianDisorder.lean` に移し、スケールの非負性・二乗公式と零・加法・実スカラー倍の性質を追加した。通常のトレース、昇順積、位相、共有 `Params` の条件は変更していない。講義ノートの `eq:Hqnormalized`・`eq:Jcovariance` と CLT 原稿の `subsec:SYK-model` にある標準係数規約を照合した。原稿の偶数 N・標準表現・q≥4・規格化トレースは抽象的な共有 API に追加しない。

- `lake env lean SYK/Model/GaussianDisorder.lean` と `+SYK.Model.GaussianDisorder:olean` は成功し、同ファイルの warning はなかった。
- `lake build Model SuperConcentration` は3194 jobsで成功した。
- `couplingScale_sq`、ハミルトニアンのアフィン性・加法・実スカラー倍・自己共役性の `#print axioms` は `propext`、`Classical.choice`、`Quot.sound` のみを示した。
- 各実係数は `J_A = couplingScale P * g_A`、各係数の分散は `(q-1)!/N^(q-1)`。利用側のノルムと集中評価は標準ガウス座標 `g_A` に関するものである。分散の新しい確率論的定理を追加したという意味ではなく、既存の標準ガウス測度とスケールの二乗公式に基づく規約の確認である。

`lake build` は3561 jobsで成功し、Blueprint の直接生成と `lake exe vbp check --site SYK/_out/site` も成功した。manifest と HTML cache は各63件、エラー0件であった。既存の汎用ガウス集中の linter warning と `density_variance_nonneg` の未使用 `[DecidableEq d]` warning は残る。`Annealed_FE` と `Universality` は今回も編集・個別検証の対象外である。

<a id="w04"></a>

## W04：標準行列表現の構成

既存の共有代数を使い、W02・W03 のガウス集中や確率的な規格化の移行とは独立して進められる。実際の同時編集範囲は全体計画で調整する。

- [x] 偶数 `N` に対する Jordan–Wigner 表現を `StandardRepresentation.lean` に構成し、次元 `2^(N/2)`、反交換関係、自己共役性を証明する。
- [x] 規格化トレースの内積について、対象とする相互作用演算子族の直交性を証明する。昇順積と位相が共有定義に一致することを確認する。
- [x] 必要な代数補題は Model 内の適切な共有層に置く。`Model` から `SuperConcentration` を import しない。既存補題を移す場合、移設元と利用側の修正は [SuperConcentration の担当部分](../SuperConcentration/EDITING_PLAN.md#w04) と合わせて統合する。
- [x] 個別検査、関連ビルド、主要定理の公理依存、次元・仮定の照合、このディレクトリ内の対応文書の更新を完了する。

担当部分の完了条件：具体的な表現と直交性が仮置きの証明なしに検査され、抽象的なマヨラナ系に標準表現の性質を暗黙に追加していない。表現の構成と直交性でコミット候補を分けても、指示単位は W04 のままとする。

### W04 の検証記録（2026-09-18）

対象は着手時コミット `4a27dd8e77e99784683f460d2d5d826adac166e3` からの未コミット差分。`StandardRepresentation.lean` に再帰的な基底 `StandardBasis m` と Jordan–Wigner 生成子を構成し、偶数 N に対する `standardMajoranaSystem` を実装した。次元は `2^(N/2)`、生成子は自己共役で共有のマヨラナ関係を満たす。講義ノートの `eq:majoranaCAR` と CLT 原稿の `subsec:SYK-model` に照合し、Pauli Y の符号、先行サイトの Z、0始まりの添字と原稿の1始まりの添字の対応を確認した。

`standardInteraction_orthonormal` は、共有の昇順積・位相をそのまま使い、同じ偶数次数 q の相互作用族について `normalizedTrace (star Ψ_A * Ψ_B) = if A = B then 1 else 0` を証明する。非対角成分は添字集合の差にある生成子による共役とトレースの巡回性から消える。この固定次数の証明に既約性の追加仮定は不要であり、異なる次数を混ぜた族の直交性は主張していない。抽象構造のフィールドや仮定は変更していない。

- `majorana_sq`、語の並べ替え・随伴との積、相互作用の二乗の既存証明を `SuperConcentration.Core` から `Model.Majorana` へ移設した。生成子が添字集合に含まれる場合・含まれない場合の交換則を共有層に追加し、逆向きの import は作っていない。
- `lake env lean SYK/Model/Majorana.lean`、`lake env lean SYK/Model/StandardRepresentation.lean`、`lake env lean SYK/SuperConcentration/Core.lean` は warning なしで成功した。`lake build +SYK.Model.Majorana:olean` と `lake build Model SuperConcentration`（3195 jobs）も成功した。関連ビルドには既存のガウス基盤・密度行列の linter warning が残る。
- 基底の次元、生成子の二乗・自己共役性・反交換関係、二つの系の構成、トレース直交性、移設・追加した共有補題、および既存の二乗和・両側集中評価に対する `#print axioms` は、すべて `propext`・`Classical.choice`・`Quot.sound` のみだった。仮置きの証明や新たな公理はない。
- 全体ビルドと Blueprint の生成・参照検査は [Chapters の W04 記録](../Chapters/EDITING_PLAN.md) に記録する。`Annealed_FE` と `Universality` は既定対象から除外されたままで、今回も検証していない。

## 利用側への接続

- W02 の汎用証明は [Probability/GaussianConcentration の計画](../Probability/GaussianConcentration/EDITING_PLAN.md)、旧配置・利用側の移行と W05 は [SuperConcentration の計画](../SuperConcentration/EDITING_PLAN.md) が管理する。
- 旧段階2にあった CLT 固有の規格化分配関数は、標準表現と集中不等式の再設計後に行う [W06](../CLT/EDITING_PLAN.md#w06) へ移した。`Z(0)=1` と共有分配関数との対応はそこで証明する。
- `Annealed_FE` は編集せず、既知の破損を履歴に残す。現在の既定ビルドには含まれないため、その成功を同ライブラリの検証結果として扱わない。
- Blueprint の編集細目は [Chapters の計画](../Chapters/EDITING_PLAN.md) が管理する。全体計画に従い、対応する実装単位内で完了する。

<a id="z01"></a>

## Z01：零点のない領域

これは W01–W06 と別の後続課題であり、必要な領域・一様性の選定前には実装へ進まない。CLT 側は要件をここへ集約し、同じ進捗チェックを持たない。

- [ ] CLT が必要とする円板・帯状領域と、一様性の対象（`N`・ハミルトニアン・逆温度）を精査する。
- [ ] 固定したハミルトニアンに対する実軸近傍など、最初に証明する具体的な領域を選定する。
- [ ] 一様な非零性を内部で証明するか、正確な外部結果を入力とするかを決め、必要な承認を得る。
- [ ] 非零性の定理から条件付き API の `Z z ≠ 0` を供給する。
- [ ] 正則な対数が必要な場合に限り、単連結性など枝を選ぶ条件を明示して構成する。

全複素平面での非零性や複素逆温度における正値性は目標にしない。完了条件は、選定した領域で必要な仮定を供給でき、外部入力と内部で証明した結果が区別されていることとする。

## 各単位の検証と記録

変更ファイルを個別に `lake env lean` で検査し、`lake build Model` と移行済み利用側の最小ビルドを行う。Model と集中不等式の接続を変更した単位では `lake build Model SuperConcentration` を実行する。重要な定理では `#print axioms` と定理文の仮定を確認する。

ワークスペース全体に影響する変更では `lake build` を実行する。Blueprint の変更では本文と宣言参照を照合し、Verso 復帰後に `lake lean SYK/BlueprintMain.lean -- --run SYK/BlueprintMain.lean --output SYK/_out/site` と `lake exe vbp check --site SYK/_out/site` を実行する。現在の既定ビルドから除外されている `Annealed_FE` と `Universality` は個別に検証済みとは扱わない。既定範囲には新規の `sorry`、`admit`、`axiom`、未解決の証明目標を許容しない。

検証記録には対象コミット・差分、コマンド、結果、警告、公理依存、残る仮定を記す。新しい検証結果は該当単位の節に追記し、過去の成功を変更後の成功として転記しない。

## 再編前の実装・検証履歴

以下は旧段階0–2の記録である。「現行」「段階」や旧パスはそれぞれの記録当時を指し、上の現状表や現在の再開順序を上書きしない。`[x]` は当時の個別項目の記録であり、W01 などの単位全体が完了したことを意味しない。旧記述の「零温度」は逆温度0の補題を指す。

### 旧段階0：現状と文書の確認

各項目は移行作業の計画であり、チェックの付いていない項目を実装済みとみなさない。現行と目標の型・規格化・ビルド対象の差は `ARCHITECTURE.md` の対応表を参照する。以下のコマンドで使う新名称は、対象の改名と Lake 設定の更新後に有効になる。

- [x] 現在公開されている識別子と、その利用箇所を列挙する。
  - 2026-09-07 時点の `Definitions.lean` の公開宣言は、模型パラメータ
    `Params`（`inverseTemperature` とその型変換に関する補題を含む）、添字の
    `InteractionIndex`・`orderedIndices`・`length_orderedIndices`、抽象代数の
    `MajoranaSystem`（`psiProduct`、`anticommute`、二つの `star_psiProduct`
    補題）、`phase`、`hamiltonian`・`hamiltonian_self_adjoint`、および有限次元行列の
    Gibbs 状態・分配関数に関する
    `gibbsOperator`・`partitionFunction`・`gibbsState` とそれぞれの零温度補題である。
  - 直接 `import` しているファイルは `SuperConcentration/Core.lean`、
    `Annealed_FE/main_result.lean`、`Chapters/Model.lean` である。
    `SuperConcentration/Main.lean` と `Gibbs.lean` は前者を通じて利用し、
    `InteractionIndex`、`MajoranaSystem`、その積・反交換補題、`phase`、
    `hamiltonian`、Gibbs/分配関数 API を参照する。特に `Main.lean` は
    `Params.β` と `Params.inverseTemperature` を参照する。
  - `Annealed_FE/main_result.lean` は `InteractionIndex`、`MajoranaSystem`、
    `phase`、`hamiltonian`、`partitionFunction`、および温度を含む `Params` を参照する。
    これは承認済みの移行対象外であり、段階1の旧 API 削除後に同ライブラリだけが
    一時的にビルド不能となる見込みである。`Chapters/Model.lean` は
    `Params`、`MajoranaSystem`、`hamiltonian`、`partitionFunction` を Blueprint に公開する。
- [x] 講義ノート、CLT 原稿、`model.txt`、Lean のソースコードの相違を記録する。
  - 講義ノートの有限次元模型は、偶数 `q >= 2`、昇順の添字組
    `I`、`ψ_I = i^(q/2) ψ_{i₁} ... ψ_{i_q}`、および
    `H_q = σ_N ∑_I g_I ψ_I` を用いる。`g_I` は独立な標準ガウス変数で、
    `σ_N² = (q - 1)! / N^(q - 1)` である。標準表現は偶数 `N` に対し
    次元 `2^(N/2)` を持ち、講義ノート後半では規格化トレース
    `τ_N = 2^(-N/2) Tr` と相互作用演算子の直交性を用いる。
  - CLT 原稿の `subsec:SYK-model` は、偶数 `N` と偶数 `q >= 4` に限定し、
    講義ノートと同じ `σ_N`、位相、ガウス係数、標準行列表現を使う。分配関数は
    `Z_N(z;G) = tr(exp(-z H_N(G)))` であり、`tr = 2^(-N/2) Tr`、
    `z : ℂ` を許すため `Z_N(0;G) = 1` となる。一方、その高温結果では
    実数 `β` を負の値も含めて用いる。これは共有模型で物理量を
    `β : ℝ≥0` に限る方針と異なるため、解析層の複素変数 API と CLT 固有の
    仮定を分離して扱う必要がある。
  - `model.txt` は現在の Lean 実装の初期設計案であり、`β >= 0` を
    `SYKParams` に格納し、非規格化 `Tr(exp(-βH))` と `β : ℝ≥0` の
    Gibbs state を提案する。ガウス型の disorder と具体的な行列表現は任意の
    後続項目で、抽象トレース代数も選択肢としている。共有模型では通常の
    トレースと複素変数を採用したため、トレースの規約は一致するが、逆温度を
    `Params` に格納する点と具体的な表現を後回しにする点は移行後の目標と一致しない。
  - 現行 Lean の `Params` は `N`、偶数で正の `q`、`q ≤ N` に加え
    `β : ℝ` と非負性を保持し、偶数 `N`、標準表現、`σ_N`、ガウス係数は
    表現しない。`MajoranaSystem`、昇順積、位相、および決定論的な
    `hamiltonian` は講義ノートの代数的部分と対応するが、ハミルトニアンに
    `σ_N` は含まれない。`partitionFunction` と `gibbsState` は
    `β : NNReal`、非規格化トレースで定義され、現行の零温度定理は
    `partitionFunction 0 H = Fintype.card d` である。したがって、原稿の
    `Z_N(0)=1`、複素解析、および規格化トレースに関する主張は未実装である。
- [x] 現在のビルド結果と、重要な定理が依存する公理を記録する。
  - 2026-09-07 にワークスペースのルートで
    `lake build Model SuperConcentration` を実行し、3193 jobs を成功として完了した。
    エラー、未解決の証明目標、`sorry`、`admit`、追加の `axiom` は報告されなかった。
  - `SuperConcentration` には既存の linter warning が残る。主なものは
    `GaussianConcentrationAux.lean` と `GaussianCovMollify.lean` の
    `refine'`、柔軟な `simp`、100 文字超過、未使用の simp 引数、および
    `Core.lean` の未使用 `DecidableEq` 仮定である。これらはビルドを失敗させず、
    今回は共有模型の API 移行と無関係なため変更しない。
  - `#print axioms` により、代数的な主要定理
    `SYK.MajoranaSystem.star_psiProduct_of_even`、
    `SYK.hamiltonian_self_adjoint`、および現行の熱力学の零温度定理
    `SYK.partitionFunction_zero` はいずれも
    `propext`、`Classical.choice`、`Quot.sound` だけに依存することを確認した。

- [x] 共有模型と集中不等式の既存宣言を棚卸しし、再設計の方針を確定する。
  - `SYK_model/model.lean` から `Model/Definitions.lean` への移動、および Lake のビルド対象名の `Model` への改名は完了している。
  - 比較元は Git コミット `1b5a64cc9860f36876cc30b1a13d66ad4bfe8047` とする。旧版は Git 履歴で保持し、現行ファイルを直接改修する。旧 API を並行して維持する別モジュール、別名前空間、互換用の別名は作らない。
  - 既存の定理文、規格化、数学的な証明の着想、検証結果は比較対象として保持する。証明スクリプトは、数学的内容を保ち、変更後の Lean 検査を通す限り、重複の除去、mathlib の利用、可読性の改善のために置き換えてよい。
  - `IsDensityMatrix` と `expectation` は `Model.FiniteDimensionalGibbs` に置き、反交換族の二乗和評価は `SuperConcentration` に残す。これにより共有模型が利用側を import する循環を作らない。
  - 汎用ガウス集中不等式には、現行の `L > 0` の結果に加え、`L = 0` を定数関数として扱う API を用意する。SYK 専用の MGF と上側・下側・両側の裾評価は、汎用結果とリプシッツ評価を接続して供給する。

### 旧段階1：比較基準と共有する代数、および有限次元行列の Gibbs 状態・分配関数

- [x] `lake build Model SuperConcentration` と主要定理の `#print axioms` を再実行し、実装直前の比較結果を記録する。
  - 2026-09-07 にワークスペースのルートで `lake build Model SuperConcentration` を実行し、3193 jobs を成功として完了した。エラー、未解決の証明目標、`sorry`、`admit`、追加の `axiom` は報告されなかった。
  - `SYK.MajoranaSystem.star_psiProduct_of_even`、`SYK.hamiltonian_self_adjoint`、`SYK.partitionFunction_zero` に対する `#print axioms` は、いずれも `propext`、`Classical.choice`、`Quot.sound` だけを表示した。
  - 既存の linter warning は `SuperConcentration` のガウス集中不等式の補助ファイル、`Core.lean`、`Main.lean` に残る。主には `refine'`、柔軟な `simp`、100 文字超過、未使用の simp 引数、未使用の `DecidableEq` 仮定であり、今回の比較基準の確認では変更しない。
- [x] `Model.Definitions`、`Model.Majorana`、`Model.FiniteDimensionalGibbs`、`Model.GaussianDisorder` の責務に従って現行宣言を再配置する。
  - `Definitions.lean` には模型パラメータと相互作用添字、`Majorana.lean` には
    抽象マヨラナ系、昇順積、位相、位相付き相互作用演算子、確定的な
    ハミルトニアンを置いた。
  - `FiniteDimensionalGibbs.lean` には密度行列と期待値、分散の非負性、
    Gibbs 演算子・分配関数・熱平衡密度行列の性質、および行列指数関数の
    トレース微分を集約した。重複元の `SuperConcentration/Gibbs.lean` は削除し、
    集中不等式固有の反交換族評価だけを `SuperConcentration/Core.lean` に残した。
  - `GaussianDisorder.lean` には相互作用係数空間、その次元、および標準
    ガウス測度を置いた。`lake build Model SuperConcentration` により移設後の
    依存関係を検査した。
- [x] 相互作用の添字、昇順積、位相、位相付き相互作用演算子、確定的なハミルトニアンを一つの定義系列に統一する。
  - `InteractionIndex` と `orderedIndices` から `MajoranaSystem.psiProduct`、
    `phase`、`MajoranaSystem.interactionOperator` を順に定め、確定的な
    `hamiltonian` を実係数による相互作用演算子の有限和として定義した。
    これは従来の `((J I : ℂ) * phase q) • psiProduct I` という各項の展開と
    同じ規格化である。
  - 相互作用演算子の自己共役性を `Model.Majorana` に置き、ハミルトニアンの
    自己共役性を各項の自己共役性から証明する依存関係に改めた。利用側の
    `normalizedHamiltonian_affine` も相互作用演算子を用いる証明へ更新した。
- [x] `IsDensityMatrix`、`expectation`、行列指数関数のトレース微分、物理的な Gibbs 状態を `Model.FiniteDimensionalGibbs` に集約する。
  - 密度行列と期待値、非負実逆温度の Gibbs 演算子・分配関数・熱平衡
    密度行列、およびアフィンな行列指数関数のトレース微分を、同ファイル内の
    三つの節として整理した。共有宣言が `SuperConcentration` 側に重複して
    いないことも全利用箇所の検索で確認した。
  - この層は SYK の模型パラメータを使わないため、`Model.Definitions` への
    不要な依存を除いた。`Model` と `SuperConcentration` のビルド、および
    主要定理の公理依存を移行後の配置で検査した。
- [x] 位相・積・可積分性・型変換の重複を一つの補題群ずつ整理する。広範な証明探索に依存する既存部分は、同じ数学的役割を保つ明示的な証明へ置き換える。
  - 生成元をマヨラナ積の右から左へ移す符号を
    `MajoranaSystem.listProduct_mul_generator`、位相の絶対値が1であることを
    `star_phase_mul_self` として `Model.Majorana` で一度だけ証明した。
    `SuperConcentration.Core` にあった同じ帰納法と位相計算を削除し、これらの
    共有補題を相互作用演算子の二乗と反交換性の証明から利用する形にした。
  - 自己共役ハミルトニアンの分配関数を実部から複素数へ戻す変換を
    `partitionFunction_eq_ofReal_re` にまとめ、熱平衡密度行列と Gibbs 期待値の
    証明に重複していた `Complex.ext` を置き換えた。方向微分評価での期待値の
    線形性も、位相と積を再展開する柔軟な `simp` ではなく、有限和・トレース・
    実数係数の複素埋め込みを列挙した証明に改めた。
  - 再配置済みの `Model` と直接の接続部である `Core.lean`・`Main.lean` を検索し、
    可積分性を個別に再証明する重複と `aesop`・`grind`・`apply_rules` が残って
    いないことを確認した。未移行の汎用ガウス集中不等式に残る可積分性証明と
    探索タクティクは `SuperConcentration/EDITING_PLAN.md` の段階1で扱う。
  - 変更した四つの Lean ファイルを個別に検査し、
    `lake build Model SuperConcentration` と主要定理の `#print axioms` を実行した。

### 旧段階2：模型の公開 API

- [x] 逆温度を模型パラメータから削除し、解析には `z : ℂ`、物理的な定理には `β : ℝ≥0` を明示引数として渡す。
  - `Params` から `β`・`β_nonneg` を削除し、`Params.inverseTemperature` と
    その型変換補題も削除した。模型パラメータは `N`・`q` と許容条件だけを持つ。
  - `gibbsOperator` と通常のトレースによる `partitionFunction` は `z : ℂ` を
    直接受ける。正値性、熱平衡密度行列、Gibbs 期待値、および
    `SuperConcentration` の物理的結果には `β : ℝ≥0` を明示的に渡す。
  - `SuperConcentration/Main.lean` の分配関数の対数、微分、リプシッツ定数、
    裾評価を新しい引数に移行した。通常のトレースによる規約は共有模型に維持する。
  - 移行対象外の `Annealed_FE/main_result.lean` は編集せず、旧 `Params` の
    `β_nonneg` フィールド指定が使えなくなった状態を既知の破損として残した。
  - 変更した Lean ファイルを個別に検査し、`lake build Model SuperConcentration`
    を成功として完了した。主要定理の `#print axioms` は従来どおり
    `propext`、`Classical.choice`、`Quot.sound` だけを表示した。
    `lake build` と `lake exe vbp build` は、移行対象外の
    `Annealed_FE/main_result.lean` が削除済みの `Params.β`・`Params.β_nonneg` を
    指定する既知の2エラーだけで失敗した。後者が成果物を生成できなかったため、
    `lake exe vbp check` は Blueprint manifest がないことを報告した。
- [x] 通常の `partitionFunction` と、必要な箇所で使う `normalizedTrace` を定義する。
  - `partitionFunction z H = Matrix.trace (exp (-z • H))` とし、`partitionFunction 0 H = Fintype.card d` を証明した。`normalizedTrace` は標準表現の直交性など、次元で規格化する量だけに用いる。

CLT 固有の規格化分配関数の未完了項目は W06 へ移した。

- [x] 整関数性と複素微分を証明し、対数微分には `Z z ≠ 0` を明示する。
  - `partitionFunction_has_deriv_at` により
    `Z'(z) = -Tr(H * exp(-zH))` を示し、全点での複素微分可能性から
    `partitionFunction_analytic_at` を導いた。
  - `partitionFunction_mul_log_deriv` は `Z z ≠ 0` の下で
    `Z z * logDeriv Z z = -Tr(H * exp(-zH))` を与える。これは零点のない
    領域の構成や複素対数の枝の選択を仮定せず、局所的な対数微分だけを記録する。
- [x] 自己共役な `H` と `β : ℝ≥0` に限定して、通常の分配関数の正値性、密度行列、ギブス期待値、実対数を定義する。
  - 自己共役な `H` に対する分配関数の正値性、通常の分配関数で規格化した密度行列、その Gibbs 期待値、および実対数を整備した。
  - `SuperConcentration` の対数分配関数も通常の規約に統一した。規格化が必要な CLT 側では、後続の局所定義と必要な変換補題で扱う。
  - 2026-09-07 に `Model/FiniteDimensionalGibbs.lean`、`SuperConcentration/Main.lean`、`Chapters/Model.lean` を個別に検査し、`lake build Model SuperConcentration` を成功として完了した。既存の linter warning に加え、`Chapters/Model.lean` には公開済み `Params` と `MajoranaSystem` のフィールドにドキュメント文字列がないという warning が残る。
  - `SYK.partitionFunction_zero`、`SYK.partitionFunction_pos`、`SYK.thermalDensity_isDensityMatrix`、`SYK.logPartition_two_sided_tail_standardGaussian` に対する `#print axioms` は、いずれも `propext`、`Classical.choice`、`Quot.sound` だけを表示した。
  - `lake build` と `lake exe vbp build` は、移行対象外の `Annealed_FE/main_result.lean` が削除済みの `Params.β`・`Params.β_nonneg` を指定する既知の2エラーだけで失敗した。同ファイルには今回導入していない既存の `sorry` も残る。後者が成果物を生成できなかったため、`lake exe vbp check` は Blueprint manifest がないことを報告した。
