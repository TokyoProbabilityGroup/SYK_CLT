# SYK 中心極限定理の編集計画

## 目的と管理範囲

この文書は `refs/CLT_SYK.tex` と `refs/sections/` から成る原稿の修正、数学的監査、および Lean 形式化の細目と完了条件を管理する。実行する単位・優先順位・状態・並列実行の調整は [全体計画](../EDITING_PLAN.md) に集約する。原稿の監査と Lean による検証の完了は別々に判定する。

文書を必要以上に増やさないため、問題一覧だけを記録する `issue_register.md` は作成せず、既知の問題をこの文書で管理する。判断記録だけを残す `decision_log.md` と作業記録だけを残す `work_log.md` も作成せず、重要な判断とその理由は該当項目または `ARCHITECTURE.md` に反映する。

## 再開時に確認する未完了事項

- 現在の `thm: input` は He2026 を引用した、すべての実数の逆温度に関する外部結果である。以前の「原稿内で大数則を証明する」計画をそのまま実行せず、R04 で引用と仮定を照合する。
- 標準化した CLT の定理文は `beta = 0` を除いていないが、本文の証明と Lean は除外している。R02 で照合する。実数の `|β|` 条件を旧方針だけで非負領域へ変更しない。
- 現行の対数 CLT は `Z_N ≥ 1` とカオス分解による証明である。集中評価を使う旧証明は `main-results.tex` の `\iffalse` 内にある。
- `AnnealedInput` の解析性・高温半径・一般表現族に対する量化と、現行原稿の全実軸上の `C¹` の外部入力との対応は未確認である。

これらは解決済みの記録ではない。定理文を変更する解決には人間の研究者の承認が必要である。

## 運用文書の整備履歴

以下は旧段階0の完了記録であり、数学的監査や形式化の完了を示さない。

- [x] 共有 Lean ワークスペース用の `AGENTS.md` を一般化する。
- [x] `SYK/workspace/AGENTS.md` を配布用テンプレートとして追加する。
- [x] `SYK/AGENTS.md` と `SYK/CLT/AGENTS.md` を追加する。
- [x] `SYK/CLT/ARCHITECTURE.md` と本計画を追加する。
- [x] 公開用の英語版 `SYK/workspace/README.md` と `SYK/CLT/README.md` を追加する。

完了条件：正式な参照元、依存関係、未完了事項、および文書の役割分担が明示されている。

<a id="r01"></a>

## R01：数学的内容を変えない原稿整理

- [ ] 旧計画で指摘した未完成の等号を現行のガウスカオス展開と再照合し、必要な修正だけを行う。2026-09-08 の目視では `eq: chaos` に展開式があるため、古い指摘だけを根拠に再編集しない。
- [ ] Lemma 3.1 と Corollary 1.3 の証明について、旧計画が指摘した重複が現存するか再照合し、残る重複を削除する。
- [ ] `paritcular` などの明らかな綴りの誤りを修正する。
- [ ] 文脈上明らかな `ell_p` と `ell'` の記号上の誤りを精査する。
- [ ] 長いコメントアウト済み旧証明の扱いを確認する。方針が未承認の間は保持し、削除が必要なら対象を示して確認する。
- [ ] LaTeX の生成物の追跡状況を確認する。2026-09-08 時点では `sections/introduction.pdf` と `sections/gaussian-chaos.pdf` が追跡されている。扱いの変更は提案して承認を得る。
- [ ] 原稿をコンパイルし、エラー、警告、および未解決の参照を報告する。

完了条件：定理文の数学的内容を変更せず、重複した記述や壊れた数式がない状態で原稿をコンパイルできる。

<a id="r02"></a>

## R02：定理文に関わる問題

現行原稿と Lean の実数 `β`・`|β|` 条件を基準に、各結果で必要な上限と端点を照合する。特に `beta = 0` の退化した相対 CLT と、分散で割るためそこで未定義となる標準化 CLT を分ける。旧計画の非負領域への統一は自動実行しない。

仮定・規格化・温度領域・外部入力の調査は承認前に行える。変更案と根拠をまとめ、定理文や採用する前提を変更する前に人間の研究者の明示的な承認を得る。調査が終わって承認を待つ場合は、ここに判断事項を記し、一覧の状態を「判断待ち」にする。非負逆温度を使う共有模型の方針だけで、原稿の正確な範囲まで承認されたとはみなさない。

- [ ] 相対ゆらぎの CLT が `beta = 0` で持つ退化した極限と、そこで未定義となる標準化した CLT のパラメータ範囲を分けて記述する。
- [ ] `thm: input`・各 CLT・内部補題について、全実軸の入力と高温に限ったゆらぎの結論を区別する。
- [ ] 原稿の `β ℓ_q'(β) > 0`（すべての非零実数）と、Lean の小さい非零逆温度での条件付き結果を照合する。
- [ ] 高次カオスに必要な `beta_Rad`、Lean の `hFE.βFE` と非退化半径、原稿に残る `tilde_beta_q` の役割を確認する。旧温度上限の一覧を無条件に再採用しない。
- [ ] He2026 の引用・規格化・表現の範囲を監査し、`AnnealedInput` を維持するための追加根拠か、原稿に合わせた変更案を示す。`C¹` から実解析性は推論しない。入力の変更は W06 に含めない。

完了条件：三つの主結果について、逆温度の範囲と非退化条件が相互に整合する。

<a id="r03"></a>

## R03：Theorem 1.2 の監査

ガウス–エルミート部分積分、偶奇則と二次カオス、行列微分、ラデマッハ評価、外部入力を調査し、仮定と定数を照合する。並行調査と同じ TeX ファイルへの修正の統合は全体計画に従う。定理文の修正には R02 の承認条件を適用する。

- [ ] Clifford 代数上の符号ゲージ変換と、各頂点の出現回数に関する偶奇則を検証する。
- [ ] `lem:Gaussian-Hermite-IBP` について、分散1のエルミート多項式の規格化、`η ≤ α` の各偏導関数だけに課された指数増大と正則性、積分の可測性・可積分性、座標ごとの部分積分と Fubini を照合する。`Z_N` への適用で必要な評価は F04 と区別する。
- [ ] 一次カオスの消滅と、二次カオスの係数の厳密な値および規格化を検証する。係数が相互作用添字によらない根拠を補い、原稿の和の計算だけで同一性を仮定しない。
- [ ] Duhamel の反復微分公式と非可換 Hölder 不等式による評価を検証する。
- [ ] ラデマッハ変数による符号化の恒等式と、指数モーメント評価の一様性を検証する。
- [ ] `O(N^(-3(q/2-1))) = o(N^(2-q))` を確認する。
- [ ] He2026 の引用箇所・規格化の変換と、現行原稿の `C¹`・導関数評価・局所一様収束の導出を確認する。旧入力の解析性との差は R02 と共有する。
- [ ] 分散の漸近挙動と、標準化した CLT を導く論理を確認する。

完了条件：現在の原稿内の結果と、明示した外部入力だけから Theorem 1.2 が証明される。

<a id="r04"></a>

## R04：外部結果 `thm: input` の照合

現行原稿はすべての実数の逆温度での大数則と微分可能性を He2026 の結果として引用する。旧計画の Borel–Cantelli による内部証明の追加は必須作業から外す。外部結果の監査と Lean での外部入力の扱いは別に判定する。

- [ ] 引用元の正確な定理文、トレース・ハミルトニアンの規格化、温度領域、概収束の確率空間を照合する。
- [ ] `ell_p` と `ell_q`、各固定 `β` に対する概収束と同時概収束、極限の微分可能性の範囲を照合する。
- [ ] CLT に必要なアニール入力と、概収束を含む外部結果全体を区別する。内部で大数則を証明する F08 を残すかは別途仕様を確定する。

完了条件：`thm: input` の引用が正確な仮定と規格化で裏付けられ、外部入力であることが明示される。

<a id="r05"></a>

## R05：Corollary 1.3 の監査

R02・R03 の該当入力の確定後に、有効な本文の新証明を監査する。分布収束だけから二次モーメントの漸近を推論せず、直交分解・剰余評価を明示的に使う。

- [ ] 確率論的な意味での対数の線形近似を検証する。
- [ ] `sup_N E S_N^4 < ∞` と剰余の二次モーメントから `P(Y_N < 1/2) = O(N^(-3a))` を導く議論を検証する（`a=q/2-1`）。
- [ ] 相互作用のトレース零と Jensen による `Z_N ≥ 1`、およびアニール入力による `log E Z_N = O(N)` を照合する。
- [ ] `h(y)=y-1-log y` を `y≥1/2` と `y<1/2` に分け、`0≤-E log Y_N=O(N^(-2a))+O(N^(1-3a))=O(N^(-2a))=o(N^(-a))` を検証する。
- [ ] `beta = 0` の扱いが、標準化した CLT に依存していないことを確認する。

完了条件：線形近似に伴うランダムな誤差と、中心化に伴う確定的な誤差が、いずれも CLT のスケールでは無視できることが示されている。

<a id="w06"></a>

## W06：現行 CLT の有限模型・モーメント・対数の基盤

### 再設計の基準（2026-09-24）

コミット `6621fedfb214cef1b1c3dead0951efdff6bb3e2d` の Lean と、親 TeX が読み込む4節を確認した。以下はソースの棚卸しであり、この再計画で Lean・LaTeX・外部文献の再検証は行っていない。9月18日の記録は履歴として保持する。

| 現在あるもの | 扱い |
| --- | --- |
| 一般の非空有限次元 `MajoranaSystem`、`Setting q`、行列の添字型の要素数 `Fintype.card d` で規格化した `partitionFunction` | 現行定義を維持する。標準表現への置き換えや重複定義はしない |
| `partitionFunction_zero`、`realPartitionFunction_zero`、通常トレースとの一致、実数性、正値性、`Setting.varianceZ_zero` | 証明項あり。W06 で現行環境の検査と公理依存を確認する |
| `Setting.partition_moments` | `sorry` が残る。W06 の主要な証明対象 |
| `AnnealedInput` と条件付きのアニール量・導関数・二次係数の極限、小温度での符号・極限分散正値性 | 再実装しない。入力と原稿の差は R02・F06 に残す |
| `partition_and_log_partition_clt` と二つの射影 | 共同定理に `sorry`。W06 の証明対象外 |
| `ConvexDerivatives.lean` | 証明項あり。ただし局所一様収束を仮定する。原稿の各点収束から両方の局所一様収束を導く補題全体ではない |
| `Preliminaries`・`CLTComponents`・`GaussianConcentration` | 実質的に雛形。最後の集中評価は現行本文では不使用 |

現行の `cor:free-energy-clt` の有効な証明は `Z_N ≥ 1` とカオス分解のモーメント評価を使う。旧集中評価と旧証明は `main-results.tex` の `\iffalse` 内であり、W06 の必須成果から集中評価の移送を外す。W05 の成果自体は維持する。

### 対象と正確な成果

有限模型では現在の `P : Params`、`M : MajoranaSystem P.N (Matrix d d ℂ)`、`[Fintype d] [DecidableEq d] [Nonempty d]` とすべての `β : ℝ` を用いる。確率測度は `standardGaussianMeasure P.N P.q`。原稿の漸近結果は引き続き固定偶数 `q≥4` と `Setting q` を使う。有限模型の定理に `AnnealedInput` や最終 CLT を仮定しない。

- [x] 既存の有限模型の定義・証明を再検査する。標準表現へ特殊化したとき、`standardBasis_card` により `normalizedTrace = 2^(-N/2) Tr` となる対応を確認する。一般表現と標準表現の分配関数が一致するという表現独立性までは証明対象にしない。
- [x] 偶数の正の次数の各相互作用のトレースが零であることから `normalizedTrace (normalizedHamiltonian P M g) = 0` を導く。既存の `interactionOperator_mul_generator_of_mem`、`majorana_sq`、トレースの巡回性を使う局所的な証明を優先し、F02 の符号ゲージ変換全体を前提にしない。
- [x] 自己共役性とトレース零から、規格化された固有値平均への Jensen により `1 ≤ realPartitionFunction P M β g` を証明する。一般行列の補題を追加する場合は Model の既存ファイルに置き、SYK の適用と分離する。
- [x] 有限次元で `Z(β,g) ≤ exp(C * ‖g‖)`（固定した模型・`β` に依存する有限定数）などの支配評価と可測性を示し、ガウス測度の既存の `integrable_exp_mul_norm` を使う。必要な結論は `MemLp (S.Z β n) 2 μ`、`Integrable (log ∘ S.Z β n) μ`、`0 < S.meanZ β n`。現在の `partition_moments` の定理文を保って `sorry` を除く。全次数の微分評価やサイズに一様な最良定数は要求しない。
- [x] `Y_N=Z_N/E Z_N` の正値性・可積分性・`E Y_N=1` と `MemLp Y_N 2 μ` を導く。`log Y_N=log Z_N-log E Z_N` とその可積分性を示し、中心化した `log Y_N` と `log Z_N` の一致を証明する。
- [x] 新証明への有限模型の受け渡しとして `0≤log Z_N`、`-log Y_N≤log E Z_N`、`0≤log E Z_N` を供給する。`log E Z_N=O(N)` と中心化誤差の漸近評価は外部入力・カオス評価を要するため F06・F07 に残す。
- [x] `β=0` で `meanZ=1`、`Y_N=1`、実対数と相対・対数ゆらぎが零になることを確認する。標準化 CLT を `β=0` に拡張しない。
- [x] README・構造文書・Blueprint の現在の定理文、入力、証明状態、現行原稿の参照との一致を確認する。

### 範囲と実行順序

主な編集対象は既存の `Main.lean` と対応文書・`Chapters/CLT.lean`。共有が必要なトレース・有限行列補題に限り `Model/Majorana.lean`・`GaussianDisorder.lean`・`FiniteDimensionalGibbs.lean` を使用し、Model の作業規則と検証も適用する。新しい構造体・ファイル・互換 API は予定しない。

順序は「既存実装の検査 → トレース零と `Z≥1` → 成長評価と `partition_moments` → 相対量・対数・零逆温度 → 統合検証」。主な入力は W01–W03、標準表現との照合には W04 を使う。W05 の集中評価、R02 の外部入力変更、F01–F07 の完成は待たない。

複素分配関数の定義は維持するが、現在使われない整関数性・複素対数微分の CLT 専用 API を一式追加することは完了条件にしない。必要な解析は利用課題で共有結果から導く。零点のない領域は Z01、任意階微分と積分交換は F04、凸性とアニール導関数収束は F06 に置く。通常トレースの対数との差 `log d` と集中評価の移送も、実際の利用が生じた際の別作業とする。

`AnnealedInput` の型・最終 CLT の定理文・`Annealed_FE`・TeX 本文は W06 で変更しない。現行 `AnnealedInput` の構築を W06 の前提にせず、有限模型の成果はこの入力にも既存の未証明定理にも依存させない。

### 完了条件と検証

変更ファイルの `lake env lean` と `lake build CLT` を行う。Model を変更した場合は `lake build Model SuperConcentration CLT` を行い、波及を確認する。W06 の有限模型の主要定理、特に `partition_moments` の `#print axioms` に `sorryAx` がないことと、定理文に未検証の前提がないことを確認する。

`CLT/Main.lean` は `Annealed_FE/main_result.lean` を直接 import するため、同ライブラリの既定対象からの除外だけでは依存先としての構築を除けない。既存の `Annealed_FE` の10箇所と共同 CLT の `sorry` は対象外として報告し、ビルド成功を最終結果の証明完了と呼ばない。対象外のエラーが検査を妨げる場合は根拠を記録し、無断で対象外へ修正を広げない。

W06 の完了は、上記の有限模型の成果・原稿との対応・[Chapters の計画](../Chapters/EDITING_PLAN.md)の更新・差分確認までとする。Verso の生成・参照検査は休止中につき行わない。今回の再計画ではこれらの証明・ビルドを実施しておらず、W06 完了ではない。

### 引き継ぎ・有限模型の検証（2026-09-26）

開始時点は `nakajima` の `b885edd`、作業ツリーはクリーンだった。`0cb8c28` にはトレース零、固有値による `Z≥1`、指数増大と `partition_moments`、零逆温度の証明が既に含まれていた。上の9月24日の棚卸しは履歴であり、現在の未証明箇所の一覧ではない。

今回、既存証明を維持して次を追加・検証した。

- `normalizedHamiltonian_normalizedTrace_eq_zero` と `partitionFunction_standard`。後者は `standardBasis_card` により通常トレースの係数を `(2^(N/2))⁻¹` とする。原稿の `subsec:SYK-model` と位相、ガウス分散、ギブス因子の符号、標準表現の次元が一致する。一般表現の外部極限定理や表現独立性は主張しない。
- `Setting.Y_memLp`・`Y_integrable`・`Y_pos`・`integral_Y` により相対量の正値性、二乗可積分性、可積分性、期待値1を得た。
- `meanZ_ge_one`・`log_meanZ_nonneg`・`log_Y_eq`・`log_Y_integrable`・`integral_log_Y`・`centered_log_Y_eq`・`neg_log_Y_le_log_meanZ` により、有効な `cor:free-energy-clt` の有限模型の対数恒等式と下界を得た。`meanLogZ` と `log meanZ` を同一視していない。`log E Z=O(N)` と中心化誤差の漸近評価は引き続き F06・F07。
- 既存の `varianceZ_zero`・`meanZ_zero`・`Y_zero`・`meanLogZ_zero`・`relativeFluctuation_zero`・`logFluctuation_zero` を再検証した。実対数が零になることは `realPartitionFunction_zero`・`Y_zero` と `Real.log_one` から従う。

検証結果：

- 初回 `lake env lean SYK/CLT/Main.lean` は古い `main_result.olean` の `incompatible header` で失敗。`lake build SYK.CLT.Main` による依存先の再構築で解消し、依存設定・バージョンは変更していない。
- 最終 `lake env lean SYK/CLT/Main.lean` と `lake build SYK.CLT.Main` は成功（3134 jobs）。`lake build SYK.Model.StandardRepresentation` も成功した。Main の警告は対象外の共同 CLT の既存 `sorry` のみ。
- Main の有限模型・Setting 部分にある公開30定理すべての `#print axioms` は `propext`・`Classical.choice`・`Quot.sound` のみ。`partition_moments`、トレース零、`Z≥1`、今回追加した相対量と対数の結果は `AnnealedInput`、最終 CLT、未検証の前提に依存しない。
- 最終 `lake build CLT` は `CLT/Lemmas/Tool.lean:1:0: unknown module prefix 'RequestProject'` で失敗した。Main はこのビルドでも成功し、失敗対象は Tool のみ。`Tool.lean` は着手前から追跡されている別課題の補助ファイルで、W06 の import 経路にない。対象を除外して成功扱いにする設定変更や、未承認の外部依存追加は行わない。GaussianIBP 等の既存 linter・非推奨警告は残る。
- 既存の共同 CLT の1箇所と `Annealed_FE` の10箇所の `sorry` は対象外。有限模型30定理の公理依存とは区別する。
- README・構造文書・Blueprint の有限模型の記述を検証済み宣言に対応させ、章の古い GaussianIBP import パスも実在する `Lemmas/GaussianIBP` に合わせた。章内の宣言参照と依存名をソース照合した。Verso は休止中であり、章の Lean 検査・生成・`vbp check` は未実施。

この引き継ぎ時点では有限模型の実装と個別検証が完了し、W06 全体は関連ライブラリの検査条件が未達だった。後続の削除・完了記録は次節を参照する。

- [x] `Tool.lean` の扱いを確定した後、`lake build CLT` を再実行し、W06 の統合検証を完了する（後続依頼による参照監査・削除で解消）。

### Tool.lean の参照監査・削除（履歴）と W06 完了（2026-09-26）

ユーザーから「本文の主張を含む他ファイルからの参照を確認し、問題なければ Tool.lean を削除し、W06 を閉じて作業記録を残す」と指示されたため、次の順で実施した。

1. **参照監査**：ワークスペース内の Lean・TeX・Markdown・Lake 設定を検索した。他の Lean に `SYK.CLT.Lemmas.Tool` の import はなく、本文・Blueprint にこのモジュールや固有宣言への参照もなかった。Tool 内の宣言名候補60件（コメントアウトされた宣言を含む）を短い名前でも検索した。同名ヒットの `hermiteMulti` は `SYK.CLT.GaussianIBP` の独立定義、`normalizedTrace` は Model または AnnealedFE の独立定義、`partitionFunction` は Model・CLT・AnnealedFE の独立定義とその利用だった。`kernel` と `reflection` は自然言語の記述であり、Tool の宣言利用ではない。README・構造文書・計画書の紹介と履歴だけが Tool を参照していた。本文に関連する題材が Tool に含まれていたことと、本文の主張がその Lean 宣言を参照・利用していることを区別した。
2. **削除と検証**：`CLT/Lemmas/Tool.lean`（834行）を削除した。削除前の内容は `0cb8c287f85e338e6b25043c228009876ca2ec35:CLT/Lemmas/Tool.lean` で参照できる。Lake の glob・依存・toolchain は変更していない。削除後の `lake build CLT` は **3171 jobsで成功**、`lake env lean SYK/CLT/Main.lean` も成功した。有限模型の公開30定理の公理依存を再確認し、すべて `propext`・`Classical.choice`・`Quot.sound` のみで `sorryAx` はなかった。
3. **記録の更新**：README・構造文書から Tool を現存する部品として扱う説明を外し、全体計画の W06 を完了に更新した。Blueprint の対応する有限模型のソース照合は前節の結果を維持し、章の計画書にもビルド障害の解消を記録した。過去の Tool の紹介・ビルド失敗は時点付きの履歴として残す。

**W06 は完了。** 有限模型・モーメント・相対量と対数の恒等式・零逆温度・標準表現との対応、個別検査・関連ビルド・公理依存・文書とBlueprintのソース照合・差分確認を終えた。共同 CLT の1箇所と Annealed_FE の10箇所の既存 `sorry`、GaussianIBP 等の既存 linter・非推奨警告は残り、最終 CLT や F01–F08 の完成を意味しない。Verso の章検査・生成・参照検査は休止規則に従って未実施。次単位には着手せず、変更は未コミット。

### Tool.lean 完成後の記録修正（2026-09-26）

上の削除は時点付きの履歴である。その後、`CLT/Lemmas/Tool.lean` は現行 mathlib だけを使う補助モジュールとして同じパスに再実装された。有限次元の特異値、von Neumann 型トレース評価、Schatten--Hölder 評価、Hermitian 行列の指数と規格化トレース指数の高階微分評価を証明し、`sorry`・`admit`・`axiom` を含まない。

親ワークスペースからの `lake -f SYK/workspace/lakefile.toml env lean SYK/CLT/Lemmas/Tool.lean` と `lake -f SYK/workspace/lakefile.toml build CLT` は成功した。前者には5件の非推奨 API・未使用 `simp` 引数の warning、後者には既存の GaussianIBP 等の linter warning が残るが、エラーはない。`Tool.lean` は現在も `Main.lean` や Blueprint から import されていないため、W06 の有限模型の成果と公理依存は変わらない。行列微分評価を CLT のカオス解析へ接続する作業は引き続き F04 に残る。

### 現行証明の再検証（2026-09-24）

ユーザーの再検証依頼により、コミット `6621fedfb214cef1b1c3dead0951efdff6bb3e2d` の数学ソースを検査した。着手時の未コミット差分は前回の再計画による6文書のみで、Lean・TeX の差分はない。今回も数学ソース・依存設定を変更していない。Lean は 4.32.2、Lake は 5.0.0-src+f3b06c7。新しい toolchain や依存は取得していない。

2026-09-24 の PATH 設定後の追加確認では、対話 Bash で `command -v lake` が成功し、`lake --version` と `lake env lean --version` が上記と同じバージョンを示した。通常の `lake env lean SYK/CLT/Main.lean` も成功し、既存の `sorry` 警告2件のみだった。初回の検証では指定 toolchain の実行ファイルを絶対パスで呼び出したが、これは当時の実行方法の記録であり、プロジェクトの必須手順ではない。

2026-09-25 の再開時は、この環境の初期 PATH から `lake` を解決できなかった。ローカルの elan 設定を読み込んだ後、指定バージョンの Lake・Lean と CLT Main の個別検査が成功し、既存の `sorry` 警告2件のみだった。これは当時の実行環境の記録であり、共同編集者の PATH 設定方法を指定しない。シェルの起動設定・toolchain・依存設定は変更していない。

| 検査（ワークスペースのルートから実行） | 結果 |
| --- | --- |
| `lake build Model SuperConcentration CLT` | 成功、3213 jobs。CLT の Main・ConvexDerivatives・CLTComponents を構築。変更のない依存先では既存のビルド成果物を利用 |
| `lake env lean SYK/CLT/Main.lean` | 成功。209行の `partition_moments` と302行の共同 CLT の `sorry` 警告2件 |
| `lake env lean SYK/CLT/Lemmas/ConvexDerivatives.lean` | 成功、警告なし |
| `lake env lean SYK/Annealed_FE/main_result.lean` | 成功、既存の `sorry` 警告10件。旧 API に関する過去のビルドエラーは今回発生しなかった |
| 一時監査ファイルによる26宣言の `#print axioms`、関連する型の `#check` と入力構造の `#print` | 成功。内訳は下表。監査用 Lean ファイルは検査後に削除 |
| `git diff --check` と Lean・TeX の差分確認 | 成功。数学ソースへの変更なし |

公理依存は以下のとおり。通常公理とは `[propext, Classical.choice, Quot.sound]` を指す。

| 宣言（名前空間を省略した箇所は CLT） | 公理依存と意味 |
| --- | --- |
| `partitionFunction_zero`、`realPartitionFunction_zero`、`partitionFunction_eq_trace_div_card`、`partitionFunction_im_eq_zero`、`realPartitionFunction_pos`、`Setting.varianceZ_zero` | 通常公理のみ。一般の非空有限次元表現に関する現在の型の下で検証済み |
| `annealedFreeEnergy_tendsto`、`annealedDerivative_tendsto`、`secondChaosCoefficient_tendsto`、`exists_small_temperature_sign`、`exists_small_temperature_variance_pos` | 通常公理のみ。ただし `hFE : AnnealedInput q` を仮定した結果 |
| `abs_slope_sub_le`、`abs_slope_sub_deriv_lt`、`convex_convergence_deriv_tendstoUniformlyOn` | 通常公理のみ。最後の定理は局所一様収束・凸性・微分可能性・極限導関数の連続性などを仮定し、コンパクト集合上の導関数の一様収束を結論とする |
| `SYK.partitionFunction_has_deriv_at`、`SYK.partitionFunction_analytic_at`、`SYK.standardMajoranaSystem`、`SYK.standardInteraction_orthonormal`、`SYK.GaussianConcentration.integrable_exp_mul_norm`、`SYK.logPartition_hasSubgaussianMGF` | 通常公理のみ。共有基盤の主要6宣言 |
| `Setting.partition_moments`、`partition_and_log_partition_clt`、`partition_clt`、`log_partition_clt` | 通常公理に加えて `sorryAx`。個別 CLT も未証明の共同定理に依存する |
| `SYK.AnnealedFE.main_pressure_result`、`SYK.AnnealedFE.main_result` | 通常公理に加えて `sorryAx`。アニール主結果も未証明 |

計20宣言は通常公理のみ、6宣言は `sorryAx` を含む。CLT の有限模型6定理は、import 先にある未完成のアニール証明に依存していない。一方、条件付き漸近5定理が受け取る `AnnealedInput` には、共通高温半径、解析性、偶性、圧力と導関数の局所一様収束、二つの小温度展開がフィールドとして残る。公理依存が通常公理だけであることは、この入力自体を証明したことを意味しない。

`Annealed_FE` の未完成10宣言は、`exists_canonicalMajorana`、`paperHamiltonian_eq_sum`、`partitionFunction_eq_exp`、`paperHamiltonian_selfAdjoint`、`annealedPartition_pos`、`annealedPartition_zero`、`chordMeasure_isProbabilityMeasure`、`phiC_real_of_real`、`exists_canonicalCCG`、`exists_betaStar`。今回の範囲で新たな `sorry`・`admit`・`axiom` は追加していない。

関連ビルドは既存のガウス基盤の警告を再表示した。保存されたビルドログ上の警告件数は StandardGaussian 265件、Smooth 174件、Lipschitz 75件で、柔軟な `simp`、`refine'`、複数目標の操作、長い行、`maxHeartbeats` の設定、不要な `simpa`、未使用の仮定・変数・`simp` 引数、旧 `integral_finset_sum` 名の非推奨警告を含む。別に `FiniteDimensionalGibbs.lean:66` の未使用 `[DecidableEq d]` 警告がある。エラーや `sorry` 以外の未解決目標は報告されなかった。

この検証は W06 の新しい補題の実装、最終 CLT の完成、原稿全体の数学的監査、He2026 の引用監査を含まない。Verso は休止中のため Blueprint の機械的検証は行っていない。W06 の次の実装箇所はトレース零・`Z≥1` と `partition_moments` であり、今回の成功を W06 全体の完了としない。

<a id="formalization"></a>

## F01–F08：後続の Lean 形式化

以下は旧段階6を分割した作業枠である。W06 の完成と対応する原稿の監査を待つ。各枠を実行可能にする前に、正確な定理文・外部入力・必要な補題・編集範囲・検証対象をこの節に記録する。仕様を確定する調査と、その後の実装を混同せず、未確定の主張を仮置きで追加しない。

| ID | 成果と照合する原稿 | 主な依存関係・完了条件 |
| --- | --- | --- |
| F01 | ガウス–エルミート展開の完全性、次数ごとの直交射影・無限和、`lem:Gaussian-Hermite-IBP` の汎用的な部分 | R03 の該当監査。SpinGlass の指数増大・部分積分の必要箇所を共有ガウス基盤へ流用し、既存の `gaussianReal_stein` と統合する。展開の完全性・射影は別に証明する。`Z_N` への適用に必要な微分・成長評価は F04 と照合する |
| F02 | 符号ゲージ変換・偶奇則と一次・二次カオスの厳密な同定。`lem: parity rule lemma`、`lem:exact-second-chaos` | F01 と必要な F04 の入力。有限の `N` で係数・規格化が原稿と一致する |
| F03 | ラデマッハ符号化と一様な指数モーメント。`lem:Rademacher-encoding` | R03 の該当監査。`N` と指数パラメータの範囲、`q` のみに依存する定数を明示する |
| F04 | 任意階の Duhamel 公式、非可換 Hölder 評価、`lem:Z-derivative-bound` | W06 と R03 の該当監査。共有すべき行列解析を CLT に複製せず、F01 の部分積分へ渡す正則性・各偏導関数の指数増大と、微分・積分交換の仮定も検査する |
| F05 | `prop:higher-chaos-closure` の剰余項評価 | F01–F04。無限和の操作と `O(N^(-3(q/2-1))) = o(N^(2-q))` を検査する |
| F06 | 凸性・アニール入力・係数漸近と相対・標準化 CLT | F02・F05、R02・R03。既存の条件付き極限補題と `ConvexDerivatives` を再利用し、各点収束から局所一様収束への不足を補う。Lean が要求する全有限サイズの分散正値性は、漸近的正値性と区別して証明する |
| F07 | 対数の線形近似、小確率事象と `Z_N≥1` による中心化誤差、`cor:free-energy-clt` | F06・W06・R05、F05 の剰余評価と二次カオスの四次モーメント。新証明の `O(N^(-2a))` を得る。集中評価の移送は前提にしない |
| F08 | 大数則の Lean 上の扱い（仕様再検討） | R04 の外部引用監査後に、外部入力として記録するか内部証明を別途行うか確定する。現行 CLT・W06 の必須前提ではない |

### 共同研究者に渡す作業票

「F 番号を実装する」という短い依頼を受けても、この表は証明可能性・入力 API の確定を意味しない。担当者は原稿の有効な本文、対応する R 監査、現行 Lean の宣言を照合し、まず対象の最初の未完了な補題群について次の欄を埋める。いずれかが確定できない場合は調査結果と未決事項を返し、推測した定理文や新しい `sorry` で実装を開始しない。

| 作業票の欄 | 必ず記録する内容 |
| --- | --- |
| 数学的仕様 | TeX ラベルと有効な本文、正確な Lean 定理文の型・量化順序・仮定・規格化・結論、原稿との差 |
| 入力と境界 | 対応する R 監査の結論、先行する検証済み宣言、外部入力の出典と未証明の範囲、担当ファイル・共有 API の編集担当者 |
| F01 の流用 | SpinGlass の対象コミット・ファイル・宣言と既存 `gaussianReal_stein` などの対応、流用する定義・証明と変更点、出典・ライセンス表示、Lean/mathlib の版差と移植後の検証。上流の証明を移植先の検証済み宣言と混同しない |
| 完了判定 | 変更ファイルの `lake env lean`、関連する最小 `lake build`、主要定理の `#print axioms` と定理文に残る仮定、原稿との照合、統合後の再検査、Blueprint 更新の引継ぎ |

F01 は共有ガウス基盤への流用・高階と多変数の部分積分・エルミート展開と射影を、個別に検証できる補題群として渡す。共有部分の編集と検証の細目は [ガウス基盤の F01](../Probability/GaussianConcentration/EDITING_PLAN.md#f01)に集約する。CLT 側では `lem:Gaussian-Hermite-IBP` を `Z_N` に適用し、F04 の正則性・成長評価との接続を確認する。この適用の待ち合わせは、汎用部分積分の完成を妨げる前提にしない。

2026-09-26 の局所確認：`GaussianIBP/GIBPMultiIndex.lean` で creation 作用素から `Polynomial.hermite` の有限積への一致と、明示的な `IBPFamily` を仮定した反復部分積分は Lean 検査済み。`GaussianIBPstandard` と `GaussianIBPHilbert` の import と個別ビルドも成功した。両ファイルの部分積分は多項式増大を仮定するため、指数増大は既存の共有 `StandardGaussian.lean` の定理を利用する。`Setting.Z` の任意階の正則性・指数増大は F04 の未証明入力であり、`Z_N` への特殊化と原稿の `lem:Gaussian-Hermite-IBP` 全体は未検証のまま。定理文を強い増大仮定に置き換えて完了扱いにしない。

同日の追加検査：共有 `pi_gaussian_stein_coord` の増大仮定を選択座標 `i` の導関数だけに弱め、`Smooth.lean` の利用箇所を更新して両モジュールをビルドした。`GIBPMultiIndex.lean` では原稿のユークリッドノルムによる指数増大からこの一座標定理への変換を Lean で検査した。これは原稿の `η ≤ α` 以外の増大評価を使わない一次の入力であり、全多重指数への反復・`Z_N` の評価完了を意味しない。原稿との照合では、エルミート規格化と有限積は一致し、旧抽象多重指数定理には `IBPFamily` という未構成の仮定が残る。

続く局所検査では、指数増大の一座標 Stein 公式から creation 作用素の部分積分を導き、その可積分性を有限積ガウス上の指数可積分性で証明した。`ExpIBPChain` を使う多重指数定理は、必要な座標列に沿う積の増大評価だけを要求し、正則性は単一の `ContDiff ℝ |α| f` から導く。旧 `IBPFamily` より原稿に近いが、原稿の各 `η ≤ α` の偏導関数評価から `ExpIBPChain` の積評価を導く補題、異なる偏導順序の一致、および `Z_N` の入力は未証明である。従って原稿と完全に同じ定理文は未完成。

追加の Lean 検査では、整数係数多項式の評価の指数増大から、各 `Polynomial.hermite` 因子、有限積、および `hermiteMulti α` 自身のユークリッドノルムによる指数増大を証明した。偏導関数との積の評価には、反復中の残りのエルミート因子とその座標導関数に対する同種の評価、および原稿の `η ≤ α` と導関数列との対応がなお必要であった。

2026-09-26、明示的な `GIBPMultiIndex.lean` 完成依頼により、上記の一般部分の残件を解消した。作業開始時の HEAD は `f133a26ab1e116b8f8b581252de9a47089c81294`、同ファイルと二つの GaussianIBP 依存ファイルは未追跡、共有ガウス基盤などには既存差分があった。それらを保持して一般定理と必要な補助証明を追加した。`coordDeriv_comm`・`partialList_perm` は有限階の正則性だけで偏導順序の一致を証明する。各接頭辞の出現回数が `α` 以下であることと `partialList_eq_partialMulti` を用い、原稿の成長仮定から `ExpIBPChain` を導いた。残りの Hermite 関数とその座標導関数は、多項式関数の四則のうち定数・座標・差・積と微分への閉性を使って指数評価する。

公開定理 `hermiteMulti_ibp_of_expGrowth` の仮定は `ContDiff ℝ (∑ i, α i) f` と、各 `η ≤ α` に対する正の `C_η` による原稿と同じユークリッドノルムの評価のみ。`IBPFamily`・`ExpIBPChain`・追加の成長仮定・無限階正則性は要求しない。`hermiteMulti_ibp_integrable` は同じ仮定で両辺の可積分性を証明し、`α = 0` と空の有限添字型も除外していない。原稿の `lem:Gaussian-Hermite-IBP`・`eq:Gaussian-Hermite-IBP` と、標準独立ガウス測度・probabilists' Hermite 規格化・偏導関数・量化範囲を照合した。ユーザーの回答に従い、`Z_N` への適用は F04 に残す。

検証：親ワークスペースで `lake -f lakefile.toml env lean SYK/CLT/GaussianIBP/GIBPMultiIndex.lean` と `lake -f lakefile.toml --no-cache build SYK.CLT.GaussianIBP.GIBPMultiIndex` が成功（3144 jobs）。通常の Lake 入口は既存の `lakefile.lean` を優先し、VersoBlueprint の Git ownership 検査で失敗したため、既存 TOML を明示した。設定・依存バージョン・Git 設定は変更していない。対象ファイルには型クラス仮定についての linter warning、依存先には既存のスタイル・非推奨 API の warning が残る。上記二つの公開定理、`coordDeriv_comm`、`partialList_perm`、`partialList_eq_partialMulti`、`hermiteMulti_eq_prod` の `#print axioms` はすべて `propext`・`Classical.choice`・`Quot.sound` のみで `sorryAx` なし。対象ファイルに `sorry`・`admit`・`axiom` はない。全 CLT の完成や F01 全体の完成を意味しない。Blueprint はソース上の対応を更新し、Verso の章検査・生成・参照検査は休止規則に従い実施していない。

F03 の符号化と指数モーメント、F04 の Duhamel 公式と行列評価も独立した補題群として渡す。F02 は偶奇則から一次・二次カオスの厳密な同定へ進める。F05 は評価補題を先に検証し、無限和・漸近を含む `prop:higher-chaos-closure` を後で統合する。F06 は既存の `ConvexDerivatives` と条件付き漸近を再利用して外部仮定と既存補題を接続し、その後に相対・標準化 CLT を統合する。F07 は対数の確率的誤差と中心化誤差を先に扱い、最後に `cor:free-energy-clt` へ統合する。各段階で先行成果や仕様が不足すれば残部を前倒しせず「前提待ち」、人間の判断が必要なら根拠を示して「判断待ち」とする。

### F01 の今回の作業票と部分検証（2026-09-26）

原稿の有効な `eq: chaos` は有限添字集合 $\mathcal I_N$ 上の独立な分散1のガウス測度で、$H_\alpha(g)=\prod_I \mathrm{He}_{\alpha_I}(g_I)$、$\alpha!=\prod_I\alpha_I!$ とする。正確な未形式化の主張は $\int H_\alpha H_\eta\,d\gamma=\alpha!\mathbf1_{\alpha=\eta}$、この族の実 $L^2(\gamma)$ における完全性、各次数 $r$ の有限次元空間への直交射影公式、および次数の部分和が $L^2$ で元の関数へ収束することである。W06 の `Setting.Z` は実値で二乗可積分である。原稿の級数の等号はこの $L^2$ の意味として実装する必要がある。`CliffordSignParity.lean` の符号対称性側は複素値の `partitionFunction` を使うため、その F02 への適用と区別する。

既存の `GaussianIBP.lean` は原稿の `lem:Gaussian-Hermite-IBP` の一般部分を証明済みであり、`CliffordSignParity.lean` は同じ probabilists' Hermite 多項式と積ガウス測度を別定義で使用する。今回の `Lemmas/GaussianChaos.lean` は二つの定義の一致を証明し、既存の部分積分・可積分性を符号対称性側の記法へ移した。さらに正次数の Hermite 関数の平均零と、二つの Hermite 関数の積の可積分性を証明した。`GaussianIBP.lean` には多項式の微分と指数増大への閉性を用いた `hermiteMulti_pair_ibp` を追加し、二つの Hermite 関数の積の期待値を多重偏導関数の期待値へ移した。新しい仮定、`sorry`、公理、TeX 本文の変更はない。着手前の作業ツリーには `Lemmas/Tool.lean` の差分があり、これは変更していない。

この段階で残る主要な証明入力は Hermite 関数同士の直交性と正確なノルム、Hermite 多項式の線形包がガウス $L^2$ に稠密であること、およびその上の射影と次数和の収束であった。直交性・ノルム・有限射影は下記の追加作業で証明した。現行 mathlib とローカル SpinGlass に完成済みのガウス Hermite $L^2$ 基底定理は見つからず、既存の部分積分と符号偶奇則だけから完全性は従わない。R03 の該当する原稿監査と、上記 $L^2$ の型・複素係数との接続を確定してから、残る不足を新しい証明で埋める。F01 全体は未完了のままである。

親ワークスペースの Lean 4.32.2 で変更した二つの Lean ファイルの `lake -f lakefile.toml env lean` が成功した。最初の `lake -f lakefile.toml build CLT` は3180 jobsで成功した。`hermiteMulti_pair_ibp` の追加後、通常のビルドは親 `.lake` 内に存在する上流 `.olean` を構築中に一時的に開けず二度失敗したため、既存の依存成果物を用いる `lake -f lakefile.toml --old build CLT` を再実行し、3179 jobsで成功した。新しい `GaussianChaos.lean` に警告はない。既存の GaussianIBP・共有ガウス基盤の linter・非推奨警告と、対象外の Main・Annealed_FE の `sorry` 警告は残る。今回追加した七つの公開宣言の `#print axioms` はすべて `propext`・`Classical.choice`・`Quot.sound` のみ。章の本文・宣言参照はソース照合し、Verso の章 Lean 検査・生成・参照検査は休止規則により行っていない。親の `.lake` へのビルド書き込みには自動審査で許可された権限昇格を使用した。

同日の追加作業：`Lemmas/GaussianHermiteOrthogonality.lean` で一次元の Hermite 対積分を高階部分積分と多項式の導関数から導き、有限積ガウスの積分公式により $\int H_\alpha H_\eta\,d\gamma=\alpha!\mathbf1_{\alpha=\eta}$ を証明した。実 $L^2$ の `hermiteLp`、有限係数和、有限添字集合の張る部分空間を定義し、係数和と直交射影が一致することを証明した。各次数の多重指数集合が有限であることも証明し、`hermiteDegreeProjection` を定義した。空の座標型と次数0も除外していない。原稿の `eq: chaos` と内積・階乗・標準ガウスの規格化を照合した。$L^2$ 完全性と次数に沿う無限和の収束は未証明である。現行 mathlib にガウス Hermite 基底の完成済み定理が見つからないため、有限射影だけから無限和の等号を導いていない。R03 の全体監査、共有 F01 の SpinGlass との詳細照合、F04 の `Z_N` への部分積分適用も未完了であり、F01 全体は未完了。

検証：親ワークスペースの Lean 4.32.2 で `lake -f lakefile.toml env lean SYK/CLT/Lemmas/GaussianHermiteOrthogonality.lean` と `lake -f lakefile.toml --old build SYK.CLT.Lemmas.GaussianHermiteOrthogonality` が成功（3152 jobs）。`#print axioms` で `hermite_pair_integral_real`、`hermiteMulti_orthogonality`、`inner_hermiteLp`、`hermiteFiniteProjection_eq_starProjection`、`mem_multiIndices_degree` はすべて `propext`・`Classical.choice`・`Quot.sound` のみ。新規ファイルに `sorry`・`admit`・`axiom` はない。新規モジュールのビルド成果物を書き込むため、親 `.lake` への権限昇格を自動審査で許可された。Blueprint は本文と宣言名をソース上で照合し、Verso の章 Lean 検査・生成・参照検査は休止規則により行っていない。

継続作業：`hermiteOrthonormal_orthonormal` で階乗ノルムから正規直交族を作り、`multiIndexDegreeEquiv` と各次数の有限和によって、$L^2$ 稠密性を一つの明示的仮定として受ける `hasSum_hermiteCoefficients`・`hasSum_hermiteDegreeProjection` を証明した。従って `eq: chaos` の無限和の収束に必要な残件は、`(Submodule.span ℝ (Set.range hermiteOrthonormal)).topologicalClosure = ⊤` という無仮定の稠密性定理である。条件付きの `HasSum` をこの稠密性の証明として扱わない。親ワークスペースで同ファイルの個別 Lean 検査と `lake -f lakefile.toml --old build SYK.CLT.Lemmas.GaussianHermiteOrthogonality`（3154 jobs）が成功した。新しい三宣言の `#print axioms` は `propext`・`Classical.choice`・`Quot.sound` のみ。Verso の章検査・生成・参照検査は休止規則により未実施。

続く稠密性の準備：`Lemmas/GaussianHermiteDensity.lean` に実係数の Hermite 多項式列を `Polynomial.Sequence` として構成し、その基底定理から任意の一変数実多項式関数が Hermite 関数の有限線形包に属することを証明した。さらに座標ごとの線形性と有限集合上の帰納法を用い、有限個の一変数多項式関数の積が多変数 Hermite 関数の有限線形包に属することを証明した。多変数単項式に関する帰納法で任意の実係数多変数多項式関数にも拡張した。ガウス $L^2$ における多項式の稠密性はまだ証明していない。新ファイルの `lake -f lakefile.toml env lean` と `lake -f lakefile.toml --old build SYK.CLT.Lemmas.GaussianHermiteDensity` が成功（最終 3158 jobs）。積および多変数多項式の線形包定理の `#print axioms` はともに `propext`・`Classical.choice`・`Quot.sound` のみ。新ファイルに `sorry`・`admit`・`axiom` はない。`Chapters/CLT.lean` に代数的な線形包と未証明の解析的稠密性を区別したノードを追加し、宣言名はソース上で照合した。Verso の章検査・生成・参照検査は休止中のため実施していない。F01 の無仮定の $L^2$ 完全性と次数和は引き続き未証明。

次の橋渡し：Hermite 関数の有限線形包を $L^2$ に送ると、対応する `hermiteLp` の有限線形包に入ることを証明した。この結果から多変数多項式関数の $L^2$ 可積分性とその `mvPolynomialLp` クラスの包含を得た。さらに多項式クラスの線形包がガウス $L^2$ に稠密なら、規格化 Hermite 族の線形包も稠密であることを `hermiteOrthonormal_dense_of_mvPolynomialLp_dense` で証明した。これにより残る解析的入力を多項式クラスの $L^2$ 稠密性として明示した。親ワークスペースで新ファイルの個別 Lean 検査と `lake -f lakefile.toml --old build SYK.CLT.Lemmas.GaussianHermiteDensity`（3158 jobs）が成功し、四つの新しい公開定理の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ。多項式クラスの稠密性自体は未証明で、F01 は未完了。

解析的稠密性への継続作業：`Lemmas/GaussianMomentDetermination.lean` で、全実パラメータの指数可積分性と全次数のモーメント一致を仮定した有限実測度の一意性を証明した。実 MGF の局所 Taylor 級数と解析関数の一致定理から MGF を一致させ、複素 MGF と特性関数の一意性を用いる。`Lemmas/GaussianPolynomialDensity.lean` では標準ガウスに関する実指数関数の $L^2$ 可積分性と、任意の $f\in L^2$ との積の可積分性を証明した。これらは直交補空間から重み付き測度を作るための入力であり、多項式の $L^2$ 稠密性をまだ証明しない。親ワークスペースで両ファイルの個別 Lean 検査と `lake -f lakefile.toml --old build SYK.CLT.Lemmas.GaussianPolynomialDensity`（3160 jobs）が成功した。四宣言の `#print axioms` はすべて `propext`・`Classical.choice`・`Quot.sound` のみ。両ファイルに `sorry`・`admit`・`axiom` はない。次は $L^2$ の直交条件から正負の重み付き有限測度のモーメント一致を導き、測度一意性を多座標へ移す必要がある。

既存の `Preliminaries.lean` は F01・F03・F04 などの雛形を、`CLTComponents.lean` は F02・F05・F06 などの雛形を同居させている。補題群が別でも、同じ共有作業ツリー上で同時編集しない。独立した作業領域で同じファイルに変更を作る場合は、補題と入力 API の担当範囲を先に固定し、統合担当が差分を直列に取り込んで再検査する。共有 Model の変更では Model の作業規則と検証も適用する。Lean 実装担当は TeX 本文・外部入力の採用方針・Blueprint の証明状態を先回りして変更しない。

並列実行の候補と条件は全体計画で管理する。F08 と F06 でアニール入力を共有する場合も、同じ入力を重複定義せず、正確な所属と依存関係を実装前に記録する。F04 の共有行列解析などを他のディレクトリに置く場合は、その編集細目を配置先の計画書へ記し、同じ ID で参照する。

`N` に依存して変わる確率空間上の分布収束と、概収束に必要な共通確率空間を定理文ごとに区別する。外部入力を仮定として受け取る定理については、Lean が検証した条件付きの結論と、入力自体の証明状態を別に報告する。

2026-09-26 のファイル整理：`Chapters/CLT.lean` の import も新モジュールへ変更した。親ワークスペースで統合ファイルの `lake -f lakefile.toml env lean SYK/CLT/GaussianIBP.lean` と `lake -f lakefile.toml build SYK.CLT.GaussianIBP` が成功した。主要な四宣言の公理依存は `propext`・`Classical.choice`・`Quot.sound` のみ。当時の `Tool.lean` による CLT ビルド失敗は、完成後の同モジュールを含む `lake -f SYK/workspace/lakefile.toml build CLT` の成功で解消した。上の個別ファイル名と検証結果は統合前の履歴として残す。Verso の章検査は休止中のため実施していない。

2026-09-26 の補助ファイル確認：`Lemmas/GaussianIBP.lean` は一般ガウス–エルミート部分積分、`Lemmas/Rademacher.lean` は有限符号平均と `rademacher_encoding`、`Lemmas/Tool.lean` は行列解析・トレース指数微分・符号ゲージと Hermite 偶奇則を含む。`Lemmas/ConvexDerivatives.lean` は既存の `convex_convergence_deriv_tendstoUniformlyOn` を持ち、局所一様収束などを仮定する。これらは補題候補の所在を明確にするもので、F01/F03/F04/F06 の完了や Main の証明状態変更を意味しない。`Tool.lean` の `RequestProject.*` imports はこのソースツリー内で解決を確認できず、CLT への統合・ビルドは未確認。個別診断では Rademacher と ConvexDerivatives にエラーなし、GaussianIBP には現行 Mathlib の非推奨 import/API 診断、Tool には import 更新要求があった。Lake によるこの4ファイルの個別検査・関連ビルドと公理依存確認は未実施。

2026-09-26 の `Tool.lean` 依存診断：`RequestProject.SingularValues`・`GaussianIBPAux`・`SchattenAux`・`ExpAux`・`MatrixRealNormed`・`DerivAux` のソースは現ワークスペースと Git 履歴に存在しない。これらの import だけを外した一時コピーの Lean 検査では、ガウス–エルミート部分積分、特異値の有限和表示、トレース・Schatten 積評価、Hermitian 指数行列の特異値・トレース公式、行列の実ノルム空間インスタンス、高階微分評価が未解決となり、Duhamel 部分にも独立した証明エラーが出た。一時コピーは削除済み。元ファイルの主張を保持して依存を置き換えるには、これらの証明を現行 mathlib と共有模型に合わせて実装・個別検査する必要がある。現時点で `Tool.lean` の Lean 検査は成功していない。

同日の後続修正：`Tool.lean` に mathlib の特異値 import と有限和への変換補題を追加し、Duhamel の導関数計算を修正した。行列の実ノルム空間インスタンスは既存の複素または実スカラーの構造から制限して与えた。Hermitian 行列の指数のトレース公式はスペクトル分解から証明し、トレースの絶対値と特異値の和の評価は `T†T` の固有基底から証明した。`diagonal ![1, 0]` の正規化 Schatten ノルムは二つの特異値を直接計算して証明した。これらの箇所は親 Lake 環境でエラーなしとなった。ファイル全体の個別検査はなお失敗し、未解決の主な入力は Schatten の積評価、指数行列の特異値公式、正規化トレース指数の高階微分評価である。未検証の定理を削除・弱化せず、これらの証明を次の検証対象とする。

同日の追加検査：Hermitian 行列指数のユニタリ対角化公式 `ExpAux.exp_smul_spectral` を追加し、単独の検査ファイル `ToolScratch.lean` では Lean 検査に成功した。`Tool.lean` に統合した後の個別検査は、`SchattenAux.holder`、`SchattenAux.mul_opNorm`、`SchattenAux.opNorm_mul`、`ExpAux.sum_sv_exp`、`DerivAux.tE` が未定義で失敗した。対角化公式はそれらの証明の基礎にはなるが、特異値公式や高階微分評価をまだ証明しない。定理文の削除・弱化、`sorry` の追加は行っていない。

続く検査で `ExpAux.trace_exp_re_pos` を追加し、Hermitian 行列指数のトレースの実部が正であることをスペクトル和から証明した。個別 Lean 検査ではこの補題にエラーは出ず、上記五つの未定義入力に関するエラーが残る。PhysLib の `QuantumInfo/ForMathlib/HermitianMat/Schatten.lean` に複素行列の Schatten–Hölder 不等式があることを確認したが、現ワークスペースの依存には含まれず、一般 `RCLike` の現行定理へ直ちに適用できるものとは扱わない。依存設定は変更していない。

さらに `ExpAux.exp_smul_posSemidef` と `ExpAux.exp_smul_posDef` をスペクトル分解と対角行列の正値性から証明した。これらは親 Lake 環境で新たなエラーを生じていない。`ExpAux.sum_sv_exp` には、正値行列の特異値の和をその固有値の和へ移す補題がなお必要である。現行 mathlib の `LinearMap.singularValues` は `T†T` の固有値の平方根で定義されており、この移行は定義の書き換えだけでは済まない。ファイル全体の個別検査には先述の五つの未定義入力が残る。

続く実装で正値作用素の `T†T` の特性多項式と固有値を計算し、`SVDAux.singularValues_fin_of_positive` を証明した。Hermitian 行列指数の特性多項式の根と Euclidean 線形写像の固有値の多重集合を照合し、任意の実関数 `f` に対する `ExpAux.sum_sv_exp` を証明した。これを用いて `normalizedSchattenNorm_exp_hermitian` の既存証明も修正した。単独の `ToolScratch.lean` の Lean 検査は成功し、二つの主要補題の `#print axioms` は `propext`・`Classical.choice`・`Quot.sound` のみだった。`Tool.lean` の個別検査で指数行列の特異値公式に関するエラーは消え、残る未定義入力は三つの Schatten 積評価と `DerivAux.tE` である。ファイル全体の Lean 検査はなお成功していない。

`CLT/Lemmas/AGENTS.md` の追加後、既存の `ToolScratch.lean` を通常の `SYK.CLT.Lemmas.ToolScratch` モジュールとして個別ビルドし、`Tool.lean` から import した。重複していたスペクトル・SVD の宣言を `Tool.lean` から除き、`ExpAux.sum_sv_exp` は sibling モジュールの証明を使う。`DerivAux.tE` は規格化トレース指数として定義し、`Matrix.traceExp` との定義的等価性を個別検査で確認した。`Tool.lean` の現在の未解決入力は三つの Schatten 積評価、`DerivAux.contDiff_tE`、`DerivAux.iteratedFDeriv_tE_bound_hermitian` である。`ToolScratch.lean` の Lake ビルドは親ワークスペースの `.lake` への書き込みが sandbox で拒否されたため、同じビルドコマンドの権限昇格を自動審査で許可された後に成功した。ファイル全体の Lean 検査はまだ失敗する。

### モジュールと対応の確認

既存の雛形で採用している TeX のラベルに基づくファイル分け、`UpperCamelCase` のモジュール名、`SYK.CLT` 名前空間を維持する。README には実在するモジュールだけを掲載する。

- [x] `lemmas/` を `Lemmas/` へ改名し、すべての import を同時に更新した（旧段階6の完了記録）。
- [ ] W06 と各形式化単位で、関係するコメント・ドキュメント文字列が定理番号ではなく TeX のラベルを参照することを確認する。

各単位で個別 Lean 検査、関連する最小ビルド、主要定理の `#print axioms` と残る仮定の確認、原稿との対応を検査する。必要な Blueprint の編集細目は Chapters の計画で管理し、同じ単位内で完了する。Verso 休止中は本文と宣言参照の照合を行い、生成・参照検査は復帰後にまとめて行う。ワークスペース全体に影響する変更では `lake build` も実行する。既定ビルドから一時的に除外されている `Annealed_FE` と `Universality` は個別に検証済みとは扱わない。

検証記録は対象コミット・差分、コマンド、結果、警告、未解決事項を該当単位に残す。最終的には相対 CLT、標準化 CLT、対数 CLT の各宣言が、原稿の正確な主張・外部入力・残る仮定と対応し、仮置きの証明なしに検査されていることを確認する。大数則は F08 の仕様確定後に、その外部入力または内部証明の状態を別に記録する。

<a id="main-statements-2026-09-18"></a>

## 2026-09-18：設定と主結果の定理文

今回の明示的な依頼は、一般 `MajoranaSystem` による分配関数の設定と、十分小さい `|β|` での分配関数・対数分配関数の CLT を `Main.lean` に記し、証明に `sorry` を許可するものである。通常の証明・非負逆温度に関する規則よりこの指示を優先した。原稿と共有模型は変更していない。

`partitionFunction` は共有の `normalizedHamiltonian`・`gibbsOperator`・`normalizedTrace` を用いる。一般表現では実際の次元で割り、標準表現の `2^(N/2)` と区別する。`Setting q` は `q ≥ 4`・偶数次数・偶数の系サイズ・`q ≤ N`・サイズの発散・非空有限次元表現を明示する。各サイズの確率空間は共有ガウス係数空間で、分布収束には mathlib の `TendstoInDistribution` を用いる。

共通の半径・微分可能なアニール極限・両 CLT を `partition_and_log_partition_clt` にまとめ、分散は `(q!/2) β² (deriv ℓ β)²` とする。`β = 0` は相対・対数 CLT の退化したガウス極限に含め、標準化は非零の `β` に限って有限模型と極限の分散正値性を明示する。個別の `partition_clt`・`log_partition_clt` は共同定理から射影する。

未証明の宣言は実逆温度での実数性・正値性、必要なモーメント、共同 CLT である。アニール極限の外部入力・カオス評価・古典的 CLT・対数への移行の証明は未実装であり、W06・F01–F08 や原稿監査を完了扱いにしない。大数則は今回の範囲外。Blueprint の CLT 節にも正確な設定・式・未証明状態を反映する。Verso 休止中のため生成・参照検査は行わない。

検証：`lake env lean SYK/CLT/Main.lean` と `lake build CLT` は成功し、追加した4宣言の `sorry` 警告が残る。上流の `StandardGaussian.lean` に既存の linter 警告・タクティク案内がある。共同 CLT・個別の両 CLT の `#print axioms` は `[propext, sorryAx, Classical.choice, Quot.sound]`、`partitionFunction_zero` と通常トレースとの一致は `[propext, Classical.choice, Quot.sound]` であった。公理検査用の一時ファイルは削除した。章の宣言参照は `SYK.CLT.Main` の import により解決する。今回の差分は作業開始時のコミットからの未コミット変更で、コミットは作成していない。

最終の `lake build CLT` は成功し、`lake env lean SYK/Chapters/CLT.lean` は警告なしで成功した。`git diff --check` は成功した。Git の LF/CRLF 変換案内は数学的・Lean 的な警告とは区別する。

`Tool.lean` の微分補助部分では、Banach 代数の指数関数について全 Fréchet 微分の Duhamel 積分表示 `Duhamel.fderiv_exp_apply` を証明した。さらに `DerivAux.contDiff_tE` を実装し、実スカラーへの制限と行列トレースの解析性から検証した。個別 Lean 検査でこの二つの宣言にエラーはない。残る未定義入力は三つの Schatten 積評価と `DerivAux.iteratedFDeriv_tE_bound_hermitian` であり、`Tool.lean` 全体の検査は未成功である。

この後段の Tool に関する診断・部分実装の記録は、完成までの履歴である。最終状態は上の「Tool.lean 完成後の記録修正」に従う。すなわち、現行の `Tool.lean` は全体として Lean 検査済みであり、同モジュールを含む CLT ビルドも成功している。

## Z01：複素平面上の零点のない領域

細目と進捗は [Model の Z01](../Model/EDITING_PLAN.md#z01) に集約する。CLT 側は必要な円板・帯状領域、一様性、内部証明か外部入力かの要件を供給する。領域が確定する前に、実逆温度の集中不等式や W06 の接続を待たせない。

全複素平面での非零性や複素逆温度の正値性は目標にしない。`Z z ≠ 0` を条件とする API と、その条件を供給する領域の定理を区別する。

## 後から分離する可能性のある文書

現時点では次を作成しない。

- `proof_status.md`：結果数が増えて `ARCHITECTURE.md` の状態記述で管理できなくなった場合に分離する。
- `issue_register.md`：問題が増えて本計画の段階別管理では追跡できなくなった場合に分離する。
- `decision_log.md`：重要な設計変更が増え、現在の文書から判断理由を追えなくなった場合に追加する。
- `work_log.md`：Git 履歴と本計画では作業履歴が不足する場合に限り追加する。
