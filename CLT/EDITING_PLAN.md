# SYK 中心極限定理の編集計画

## 目的と管理範囲

この文書は `refs/CLT_SYK.tex` と `refs/sections/` から成る原稿の修正、数学的監査、および Lean 形式化の現行の細目と完了条件を管理する。実行する単位・優先順位・状態・並列実行の調整は [全体計画](../EDITING_PLAN.md) に集約する。完了済み作業の詳しい検証記録は [作業履歴](../WORK_HISTORY.md) に置き、必要な節だけ参照する。原稿の監査と Lean による検証の完了は別々に判定する。

既知の問題と重要な判断は該当する作業節または `ARCHITECTURE.md` に記録する。独立した問題一覧・判断記録は作らない。

## 再開時に確認する未完了事項

- 現在の `thm: input` は He2026 を引用して標本ごとの概収束まで述べるが、He2026 の直接の結論はアニール圧力と期待クエンチ圧力の極限である。定理を弱めるか集中評価で補うかは R04-A の判断待ちであり、以前の「原稿内で大数則を証明する」計画をそのまま再開しない。
- 標準化した CLT の定理文は `beta = 0` を除いていないが、本文の証明と Lean は除外している。標準化の範囲だけを変更する案は R02-A の判断待ちであり、実数の `|β|` 条件を非負領域へ変更しない。
- 現行の対数 CLT は `Z_N ≥ 1` とカオス分解による証明であり、R05 の監査を完了した。集中評価を使う長いコメントアウト済み旧証明は現行ソースに存在しない。
- CLT のアニール入力は He2026 を直接仮定するのでなく、`refs/sections/main-results.tex` の `prop:annealed-free-energy`（Proposition 4.2）とする。同命題の証明が使う He2026 の結果は R03、別の `thm: input` は R04 で監査済みである。
- `Main.lean` の `AnnealedInput q S` は Proposition 4.2 の偶・凸な `C¹` 関数、全実軸での局所一様収束、明示的評価、非零逆温度での符号を一つの `Setting q` について記録する。旧構造の実解析性・共通高温半径・全 `Setting q` への一括量化は除いた。原稿の模型族を具体的な `Setting q` に対応付け、入力の値を構築する作業は未完了である。

解決済みの入力構造の変更と、残る原稿監査・模型族への適用を区別する。今後さらに定理文を変更する場合は人間の研究者の承認を得る。

運用文書の整備履歴は [作業履歴](../WORK_HISTORY.md#clt-docs) に保存した。

<a id="r01"></a>

## R01：数学的内容を変えない原稿整理

- [x] `eq: chaos` には完全な展開式があり、未完成の等号は現存しないことを確認した。引数の区切り `:` を `;` に直したが、数式の内容は変更していない。
- [x] `lem:Gaussian-Hermite-IBP` と `cor:free-energy-clt` の証明は各一つだけであり、旧計画が指摘した重複は現存しないことを確認した。
- [x] `sometime`、`resutls`、`Y_n` などの明らかな綴り・添字の誤りを修正した。`paritcular` は現行ソースに存在しなかった。
- [x] `thm: input` の `ell_p` を `ell_q`、Corollary の `beta_p` を `beta_q` に修正した。導関数の `ell_q'` は正しく、変更していない。
- [x] `refs/sections/` に `\iffalse` その他の長いコメントアウト済み旧証明は現存しないことを確認した。監査では削除を行っていない。
- [x] 2026-09-27 時点で `CLT/refs/` 以下の LaTeX 生成 PDF は追跡されていないことを確認した。原稿や追跡対象の変更は別途、対象を示して扱う。
- [x] `latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=<一時ディレクトリ> CLT_SYK.tex` を実行した。2回の `pdflatex` 後に成功し、未解決の参照・引用、Overfull/Underfull、LaTeX/Package 警告はない。

完了条件：定理文の数学的内容を変更せず、重複した記述や壊れた数式がない状態で原稿をコンパイルできる。

2026-09-27 に完了。生成物は一時ディレクトリだけに置き、`refs/` には追加していない。

<a id="r02"></a>

## R02：定理文に関わる問題

現行原稿と Lean の実数 `β`・`|β|` 条件を基準に、各結果で必要な上限と端点を照合する。特に `beta = 0` の退化した相対 CLT と、分散で割るためそこで未定義となる標準化 CLT を分ける。旧計画の非負領域への統一は自動実行しない。

仮定・規格化・温度領域・外部入力の調査は承認前に行える。変更案と根拠をまとめ、定理文や採用する前提を変更する前に人間の研究者の明示的な承認を得る。調査が終わって承認を待つ場合は、ここに判断事項を記し、一覧の状態を「判断待ち」にする。非負逆温度を使う共有模型の方針だけで、原稿の正確な範囲まで承認されたとはみなさない。

- [x] 相対・対数 CLT は `beta = 0` で退化極限として意味を持つ一方、標準化した量は分散零のため未定義であることを確認した。現行の Theorem は三者を同じ範囲で述べており、下記の判断事項 R02-A が残る。
- [x] `thm: input` と `prop:annealed-free-energy` は全実軸（He2026 の正温度結果をガウス対称性で延長）、三つの CLT は `|β|<β_q`、剰余評価は `|β|<β_{\rm r}` であることを区別した。
- [x] 原稿の `β ℓ_q'(β) > 0` は Proposition 4.2 内で全非零実数について導出され、Lean の `AnnealedInput.sign` も同じ全実軸の入力を受ける。Lean の主 CLT が非零小温度だけで使うこととは矛盾しない。
- [x] 現行原稿には `\widetilde\beta_q` は存在せず、剰余評価の `β_{\rm r}` が唯一の明示的な高温半径である。主結果には `0<β_q≤β_{\rm r}` を選べばよく、別の旧半径を復活させる根拠はない。
- [x] `prop:annealed-free-energy` に合わせ、`Main.lean` の `AnnealedInput q S` を全実軸の局所一様収束、凸性・`C¹`、導関数・圧力の明示的評価、非零での符号に改めた。実解析性・共通半径・全 `Setting q` の一括量化を除いた。命題の証明中の He2026 の引用監査は R03、`thm: input` の引用監査は R04 に残る。
- [x] 旧 `AnnealedFreeEnergyLimit` を `Annealed_FE/main_result.lean` から除き、Blueprint の宣言参照を `SYK.CLT.AnnealedInput` に変更した。

完了条件：三つの主結果について、逆温度の範囲と非退化条件が相互に整合する。

判断事項 R02-A（研究者の承認待ち）：`thm:partition-clt` を、相対 CLT は `|β|<β_q`、標準化 CLT は `0<|β|<β_q` と分ける。これは Lean の `partition_clt` と証明本文に一致するが、定理文の変更なので監査では実施していない。有限サイズの分散正値性は、原稿では極限係数の非退化性から十分大きい `N` について従う範囲までしか明記されておらず、Lean が要求する `∀ n, 0 < varianceZ β n` の構築は F06 に残る。

判断事項 R02-B（F06 の入力境界）：He2026 は標準既約表現の模型族に対する命題を与える。現行 `AnnealedInput q S` は一つの一般 `Setting q` に同じ結論を仮定するが、任意の一般表現に外部結果を移す根拠はない。標準表現から作る具体的な `Setting q` へ適用するか、表現独立性を別に証明する必要がある。

<a id="r03"></a>

## R03：Theorem 1.2 の監査

ガウス–エルミート部分積分、偶奇則と二次カオス、行列微分、ラデマッハ評価、外部入力を調査し、仮定と定数を照合する。並行調査と同じ TeX ファイルへの修正の統合は全体計画に従う。定理文の修正には R02 の承認条件を適用する。

- [x] Clifford 代数上の符号ゲージ変換と、各頂点の出現回数に関する偶奇則を検証する。
- [x] `lem:Gaussian-Hermite-IBP` について、probabilists' Hermite、分散1、`η ≤ α` の各偏導関数の指数増大、可測性・可積分性、座標ごとの部分積分を照合した。一般部分は共有 Lean の `hermiteMulti_ibp_of_expGrowth` と一致し、`Z_N` の任意階評価との接続は F04 に残る。
- [x] 一次カオスの消滅と、二次カオスの係数の厳密な値および規格化を検証する。係数が相互作用添字によらない根拠を補い、原稿の和の計算だけで同一性を仮定しない。
- [x] 反復 Duhamel 公式では `r!` 個の順列と単体体積 `1/r!` が相殺し、規格化 Schatten Hölder と `‖ψ_I‖∞=1` から係数1の微分評価が得られることを確認した。
- [x] ラデマッハ符号化は多項定理と頂点ごとの偶奇で正確である。Newton 恒等式、Hoeffding 評価、`0≤t≤c_qN^{-(q-1)}` の範囲から、定数が `q` のみに依存する一様な指数モーメント評価が得られる。
- [x] `a=q/2-1≥1` に対して `N^{-3a}=o(N^{-2a})=o(N^{2-q})` を確認した。
- [x] He2026 v3 の Theorem 1.1、Theorem 2.5、Proposition 3.3 と照合した。`H_N^{He}=2^{-q/2}H_N`、`s=2^{q/2}|β|`、規格化トレース、Lehmann 測度の二次モーメント、導関数公式は一致する。各点収束から局所一様収束と導関数収束への凸性による導出も正しい。
- [x] 直交分解から分散漸近が従い、`β≠0` では極限係数が非零なので標準化 CLT が従うことを確認した。`β=0` の定理文と全有限サイズの正値性は R02-A・F06 に分離した。

完了条件：現在の原稿内の結果と、明示した外部入力だけから Theorem 1.2 が証明される。

2026-09-27 に証明監査を完了。`lem:exact-second-chaos` の原稿には、対角 Hermite 係数が相互作用添字に依らない理由をサイト置換・ガウス符号対称性から追記した。定理文の範囲変更は R02-A の承認待ちである。

<a id="r04"></a>

## R04：外部結果 `thm: input` の照合

現行原稿はすべての実数の逆温度での大数則と微分可能性を He2026 の結果として引用する。旧計画の Borel–Cantelli による内部証明の追加は必須作業から外す。外部結果の監査と Lean での外部入力の扱いは別に判定する。

- [x] He2026 v3 の Theorem 1.1 は、固定した `β>0` についてアニール圧力と期待クエンチ圧力の極限を与える。規格化トレースと `H_N^{He}=2^{-q/2}H_N` は一致するが、標本ごとの概収束は同定理の直接の結論ではない。
- [x] `ell_p` は `ell_q` に修正した。He2026 は各固定正温度の決定論的極限を述べ、負温度はガウス対称性、零温度と `C¹(ℝ)` は Proposition 4.2 の原稿内議論で補われる。同時全 `β` の概収束は引用からは得られない。
- [x] CLT が用いるのは `prop:annealed-free-energy` のアニール極限・導関数極限であり、`thm: input` の標本ごとの概収束ではない。F08 で内部 LLN を必須化しない方針を維持する。

完了条件：`thm: input` の引用が正確な仮定と規格化で裏付けられ、外部入力であることが明示される。

判断事項 R04-A（研究者の承認待ち）：`thm: input` の概収束を He2026 の直接引用として残すことはできない。選択肢は、(i) 定理を決定論的なアニール・期待クエンチ圧力の極限へ弱める、または (ii) 偶数サイズを一つの積確率空間に結合し、Gaussian concentration と Borel--Cantelli による固定 `β` の概収束を原稿内で補題として証明する、のいずれかである。CLT の証明はこの選択に依存しない。

<a id="r05"></a>

## R05：Corollary 1.3 の監査

R02・R03 の該当入力の確定後に、有効な本文の新証明を監査する。分布収束だけから二次モーメントの漸近を推論せず、直交分解・剰余評価を明示的に使う。

- [x] `N^a(Y_N-1)` の tightness と `Y_N-1→0` in probability から、局所二次評価を用いて `N^a(log Y_N-(Y_N-1))→0` in probability が従うことを確認し、積の評価を本文に明記した。
- [x] `E(g²-1)²=2`、`E(g²-1)⁴=60` から `E S_N⁴=3+12/M_N≤15` を明記した。`c_N=O(N^{-a})` と `‖R_N‖₂²=O(N^{-3a})` から `P(Y_N<1/2)=O(N^{-3a})` が従う。
- [x] 相互作用のトレース零、規格化トレースに対する Jensen の不等式から `Z_N≥1` が従う。Proposition 4.2 の固定 `β` における圧力収束から `log E Z_N=O(N)` が従う。
- [x] `h(y)=y-1-log y` の二事象への分割を照合し、`a≥1` から `O(N^{1-3a})=O(N^{-2a})`、従って中心化誤差が `o(N^{-a})` になることを確認した。
- [x] `β=0` では `Z_N=Y_N=1` なので対数 CLT は自明であり、標準化 CLT を用いない。

完了条件：線形近似に伴うランダムな誤差と、中心化に伴う確定的な誤差が、いずれも CLT のスケールでは無視できることが示されている。

2026-09-27 に完了。本文の剰余評価を Proposition 3.3 の強い `O(N^{-3a})` のまま使用するよう整理し、導出を明記した。

<a id="w06"></a>

## W06：現行 CLT の有限模型・モーメント・対数の基盤

2026-09-26 に完了。`CLT/Main.lean` の有限模型30定理について定理文・公理依存を照合し、既定の `lake build` が成功した。共同 CLT と射影には既存の `sorryAx` が残る。[検証・統合監査の記録](../WORK_HISTORY.md#clt-w06)を参照する。

<a id="integration-audit-2026-09-26"></a>

### W06 後の統合課題

`Lemmas/CliffordSignParity.lean` の宣言名衝突は共有 `SYK.partitionFunction` の直接利用で解消し、F01 の `GaussianChaos.lean` と `Main.lean` の同時 import は成功した。符号対称性と `Setting.Z` の規格化、スケール、実部、ガウス測度、Hermite 定義の接続は F02 で検証済みである。F03 の偶多重指数の符号化恒等式と、F04 の `TraceExpDerivatives.lean` から `Setting.Z` への接続も未完了である。元の障害は [統合監査](../WORK_HISTORY.md#clt-w06)、解消の検査は [F01 取り込み検証](../WORK_HISTORY.md#merge-f01-2026-09-27) を参照する。

<a id="formalization"></a>

## F01–F08：後続の Lean 形式化

以下は旧段階6を分割した作業枠である。W06 は完了済みであり、残る着手条件は各成果に対応する原稿監査・入力の確定・補助モジュールの接続である。各枠を実行可能にする前に、正確な定理文・外部入力・必要な補題・編集範囲・検証対象をこの節に記録する。仕様を確定する調査と、その後の実装を混同せず、未確定の主張を仮置きで追加しない。

| ID | 成果と照合する原稿 | 主な依存関係・完了条件 |
| --- | --- | --- |
| F01 | ガウス–エルミート展開の完全性、次数ごとの直交射影・無限和、`lem:Gaussian-Hermite-IBP` の汎用的な部分 | 完了。R03 の該当監査、SpinGlass・既存 API との照合と共有配置、直交性・階乗ノルム、有限射影、$L^2$ 完全性と無限次数和を検証済み。`eq: chaos` はガウス $L^2$ の等式として解釈する。`Z_N` への特殊化は F04 に残る |
| F02 | 符号ゲージ変換・偶奇則と一次・二次カオスの厳密な同定。`lem: parity rule lemma`、`lem:exact-second-chaos` | F01 と必要な F04 の入力。有限の `N` で係数・規格化が原稿と一致する |
| F03 | ラデマッハ符号化と一様な指数モーメント。`lem:Rademacher-encoding` | R03 の該当監査。`N` と指数パラメータの範囲、`q` のみに依存する定数を明示する |
| F04 | 任意階の Duhamel 公式、非可換 Hölder 評価、`lem:Z-derivative-bound` | W06 と R03 の該当監査。共有すべき行列解析を CLT に複製せず、F01 の部分積分へ渡す正則性・各偏導関数の指数増大と、微分・積分交換の仮定も検査する |
| F05 | `prop:higher-chaos-closure` の剰余項評価 | F01–F04。無限和の操作と `O(N^(-3(q/2-1))) = o(N^(2-q))` を検査する |
| F06 | 凸性・Proposition 4.2 のアニール入力・係数漸近と相対・標準化 CLT | F02・F05、R02・R03。`Main.lean` の `AnnealedInput q S` は `prop:annealed-free-energy` の結論を一つの模型族に対して記録する。原稿から具体的な `Setting q` への適用を確立し、既存の条件付き極限補題と `ConvexDerivatives` を再利用する。命題の証明中の各点収束から局所一様収束への導出は R03 で監査する。Lean が要求する全有限サイズの分散正値性は、漸近的正値性と区別して証明する |
| F07 | 対数の線形近似、小確率事象と `Z_N≥1` による中心化誤差、`cor:free-energy-clt` | F06・W06・R05、F05 の剰余評価と二次カオスの四次モーメント。新証明の `O(N^(-2a))` を得る。集中評価の移送は前提にしない |
| F08 | 大数則の Lean 上の扱い（仕様再検討） | R04 の外部引用監査後に、外部入力として記録するか内部証明を別途行うか確定する。現行 CLT・W06 の必須前提ではない |

### 担当別作業票とコード整理

配置整理の方針（2026-09-27）：主要補題への入口は [構造文書の索引](ARCHITECTURE.md#補助-lean-ファイルの役割)に整理した。ディレクトリ再配置と参照専用の短い Lean API ファイルの新設は保留する。索引と部分読み取りでも繰り返し探索の負担が残る場合に、実際の利用箇所を根拠に再検討する。同じ定理を再掲するだけの宣言は追加しない。

以下は共同研究者へ切り出せる成果単位であり、F01–F08 全体の状態は [全体計画](../EDITING_PLAN.md) だけで管理する。原稿監査が未了の票は、正確な定理文と入力を照合してから実装する。割当には各票への直接リンクと、[別環境への引き継ぎ手順](../EDITING_PLAN.md#別環境への引き継ぎ)を添える。

| 調査・実装 | 接続・統合 |
| --- | --- |
| [R02/R04 外部入力](#ticket-r02-r04) · [R03 分野別監査](#ticket-r03) · [F01-G 共有配置](#ticket-f01-g) · [F01-H 展開・射影](#ticket-f01-h) · [F03-R 符号化恒等式](#ticket-f03-r) | [F02-P 衝突解消済み](#ticket-f02-p) · [F04-M 行列解析](#ticket-f04-m) · [F02–F07 統合](#ticket-integration) |

<a id="ticket-r02-r04"></a>

#### R02/R04：外部入力の監査

直ちに読み取り着手できる。R02 は `refs/sections/main-results.tex` の `prop:annealed-free-energy`（Proposition 4.2）と `Main.lean` 内の `SYK.CLT.AnnealedInput` を照合し、原稿の模型族から具体的な `Setting q` への適用を監査する。R03 は同命題の証明が引用する He2026 を監査する。R04 は別の `thm: input` の引用を監査する。逆温度の範囲、規格化、極限の種類、正値性、表現の範囲、概収束に必要な確率空間、原稿内の命題と外部論文の境界を、出典・TeX ラベル・Lean 宣言名つきで返す。定理文・前提の変更案は研究者の判断へ渡す。

<a id="ticket-r03"></a>

#### R03：分野別の証明監査

直ちに読み取り着手できる。ガウス–エルミート、ラデマッハ、行列微分・符号偶奇を原稿の有効な本文ごとに分担し、各補題の量化・規格化・可積分性・極限操作と、既存 Lean 定理が証明した範囲を対照表にする。反例候補と未確定の仮定を明記し、対象票へ結果を渡す。

<a id="ticket-f01-g"></a>

#### F01-G：ガウス部分積分の共有配置と整理

読む箇所：`refs/sections/gaussian-chaos.tex` の `lem:Gaussian-Hermite-IBP` と `eq:Gaussian-Hermite-IBP`、[構造文書の依存関係と流用候補](ARCHITECTURE.md#依存関係と実装の分担)、[共有基盤の F01](../Probability/GaussianConcentration/EDITING_PLAN.md#f01)。現行宣言は共有基盤の `StandardGaussian.lean` にある `gaussianReal_stein`・`pi_gaussian_stein_coord` と、`Smooth.lean` に移設済みの `hermiteMulti_ibp_of_expGrowth`・`hermiteMulti_ibp_integrable` を参照する。完了済み証明の詳細が必要な場合だけ [作業履歴](../WORK_HISTORY.md#clt-f01-gaussian) を読む。

`GaussianIBP.lean` の高階の一般部分と `hermiteMulti_pair_ibp` は `../Probability/GaussianConcentration/Smooth.lean` に移した。共有 `pi_gaussian_stein_coord` を使い、原稿の `η ≤ α` の仮定を保つ。CLT 利用側の import と Blueprint の宣言参照も更新し、変更した Lean ファイルの個別検査、主要宣言の公理依存検査、`lake -f lakefile.toml --old build CLT` は成功した。SpinGlass の候補は分散一般の一次元公式と指数増大の補助 API だが、今回の標準分散1の証明には既存の `gaussianReal_stein` で足りるため、上流コードは流用していない。約6,500行の前半は独立した既存 API として残し、局所的な参照調査だけを根拠に削除しない。

<a id="ticket-f01-h"></a>

#### F01-H：展開の完全性と射影

`refs/sections/gaussian-chaos.tex` の `eq: chaos` に対し、`Lemmas/GaussianChaos.lean` は二つの Hermite・ガウス測度の規格化を照合した。`GaussianHermiteOrthogonality.lean` の直交性・階乗ノルム・有限射影、`GaussianHermiteDensity.lean` の多項式の有限線形包への包含、`GaussianMomentDetermination.lean` のモーメント一意性も Lean 検査済みである。`GaussianPolynomialDensity.lean` では有限積ガウス $L^2$ の多項式稠密性、Hermite 完全性、無限次数和の収束を無条件に証明した。検証の詳細は [F01 の新しい記録](../WORK_HISTORY.md#clt-f01-completion-2026-09-27) に記す。

一変数ガウス $L^2$ の単項式稠密性 `gaussianMonomialLp_dense` を証明し、有限積では各連続線形写像への射影のモーメント一意性と特性関数の一意性から `mvPolynomialLp_dense` を証明した。これで `hermiteOrthonormal_dense_of_mvPolynomialLp_dense` の仮定を供給し、`hasSum_hermiteCoefficients_unconditional` と `hasSum_hermiteDegreeProjection_unconditional` を証明した。両結論はガウス $L^2$ での収束である。原稿の `eq: chaos` は、直前の完全直交基底の記述に従い、研究者の確認を得てガウス $L^2$ の等式と解釈する。点ごとの収束は F01 の主張に含めない。

R03 の対象範囲として原稿の Hermite とガウス測度の規格化、実 $L^2$ の係数と原稿の階乗係数を照合した。共有 API の配置を統合して CLT の import を再確認した。`GaussianChaos.lean` と `Main.lean` の同時 import、CLT ビルド、主要宣言の公理依存は検査済みである。符号結果と `Setting.Z` の数学的接続は [F02 の統合](#ticket-integration)、`Z_N` への部分積分の特殊化は F04 に渡す。Verso の機械的検査は休止中であり、Blueprint の宣言参照はソース上で照合する。

<a id="ticket-f03-r"></a>

#### F03-R：ラデマッハの符号化恒等式

読む箇所：`refs/sections/higher-chaoses.tex` の `lem:Rademacher-encoding`、`eq:even-sum-Rademacher-moment`、`eq:Rademacher-exponential-moment` と、`Lemmas/Rademacher.lean` の `rademacher_encoding`。この Lean 定理は指数付き三次モーメント評価を証明済みであり、偶多重指数の和と符号モーメントの恒等式は未実装である。

R03 で有限和・偶多重指数・次数の範囲を照合してから同ファイルを編集する。既存の指数モーメント評価を保持し、恒等式を別に検査する。変更ファイルの個別検査、CLT ビルド、主要定理の公理依存を渡す。

<a id="ticket-f02-p"></a>

#### F02-P：分配関数の宣言名衝突（解消済み）

読む箇所：`refs/sections/gaussian-chaos.tex` の `lem: parity rule lemma`、[構造文書の現行実装との差](ARCHITECTURE.md#現在の実装と原稿との差)、`Main.lean`、`Lemmas/CliffordSignParity.lean`、`Lemmas/GaussianChaos.lean`、`../Model/FiniteDimensionalGibbs.lean`。元の衝突と規格化の差は [統合監査](../WORK_HISTORY.md#clt-w06)、解消の検査は [F01 取り込み検証](../WORK_HISTORY.md#merge-f01-2026-09-27)に記録した。

補助モジュール内で重複していた分配関数定義を除き、符号ゲージ不変性と偶奇則で共有 `SYK.partitionFunction` を直接使うようにした。仮定・量化順序・数学的結論は保ち、個別検査、`Main.lean` と `GaussianChaos.lean` の同時 import、主要二定理の公理依存を確認した。通常トレース、スケール、実部、ガウス測度、Hermite 定義の `Setting.Z` への接続は後続の F02 統合に渡す。

<a id="ticket-f04-m"></a>

#### F04-M：行列解析の接続と整理

`Lemmas/SingularValues.lean`、`Lemmas/MatrixTraceExponential.lean` と `Lemmas/TraceExpDerivatives.lean` の一般行列結果は Lean 検査済みであり、F02 で一次微分評価を `PartitionDerivatives.lean` の `Setting.Z` に接続した。任意階の接続は未完了である。R03 の行列微分監査後、[構造文書の依存関係](ARCHITECTURE.md#依存関係と実装の分担)、この二つの補題 file、`Main.lean`、[Model 側の F04](../Model/EDITING_PLAN.md#f04-model)を照合する。Model の編集担当を固定し、`SingularAux.singularValues_of_positive` と `SVDAux.singularValues_fin_of_positive`、汎用と共有の `normalizedTrace`、Main の局所トレース指数結果の型と利用箇所を比較する。数学的に同じ結果だけ整理し、スカラー型や規格化の差を保つ。

`β`・`couplingScale P`、実部、測度、任意階の正則性・指数増大を `Setting.Z` に接続する。変更ファイルの個別検査、必要な Model と CLT のビルド、公理依存を報告する。

<a id="ticket-integration"></a>

#### F02–F07：先行成果の統合

主定理への接続時には、`Main.lean` から補助モジュールを import する前に共通定義・基本結果を分離する。現状では補助側が `Main.lean` に依存しているためであり、現在の import に循環があるわけではない。候補は `CLT/Basic.lean` 一つとし、`AnnealedInput` とその帰結の移設範囲は利用箇所から決める。宣言名・定理文・証明を維持し、import と参照文書を更新する。個別検査、CLT と既定ビルド、主要定理の型と公理依存の照合を統合作業に含める。この整理の実施は接続時まで保留する。

各 F の原稿監査と先行成果が揃ってから、上の依存順に着手する。`Preliminaries.lean` と `SecondChaos.lean` には F02 の有限サイズ結果を実装済みで、`GaussianConcentration.lean` は宣言のない雛形である。F05 は評価補題から剰余へ、F06 は既存の `ConvexDerivatives` と条件付き漸近から主結果へ、F07 は対数の誤差評価から最終定理へ進める。原稿との照合、主要定理の公理依存、CLT と既定ビルドを報告する。

F02 完了（2026-09-27）：`Preliminaries.lean` は規格化模型への符号対称性・偶奇則・一次カオス零と、符号付き頂点転置による対角係数の添字独立性を証明した。`PartitionDerivatives.lean` は `Setting.Z` の滑らかさ、一次微分の指数増大、ガウス部分積分、放射方向微分恒等式、期待値との微分交換を証明した。`SecondChaos.lean` の `Setting.Y_secondChaos_eq` は任意の実数 `β` と有限サイズで、原稿 `lem:exact-second-chaos` の係数 `β * deriv (log meanZ) / (2 * choose N q)` をガウス $L^2$ の等式として与える。対称性・微分交換を追加仮定として受け取らず、`AnnealedInput` も使わない。

R03 の今回の監査では、原稿で省略されていた対角係数の添字独立性を転置の推移性から補った。規格化トレース、`couplingScale`、実部、二つのガウス測度、`H₂(x)=x²-1` と階乗 `2` を照合した。一次の部分積分だけで F02 に十分であり、任意階の導関数評価・部分積分の特殊化は F04 に残る。今回 `Main.lean` から補助モジュールを import する必要はなく、`Basic.lean` への分離はまだ行わない。個別検査、CLT ビルド、主要8宣言の公理依存検査、既定ビルドは成功した。詳細と既存警告・環境の範囲は [検証記録](../WORK_HISTORY.md#clt-f02-completion) を参照する。Blueprint はソース照合のみで、Verso の機械的検査は未実施。

F01-G と F04-M の整理は、その数学的成果を受け渡す段階で行う。定義の型・規格化・利用先が異なる場合は違いを記録する。R03 の結果から主張の修正が必要になっても、既存の定理文を黙って変えない。各担当者は開始ソース、編集ファイル、正確な入力宣言、検査結果を統合担当へ渡す。

### 担当票で確定する事項

「F 番号を実装する」という短い依頼を受けても、この表は証明可能性・入力 API の確定を意味しない。担当者は原稿の有効な本文、対応する R 監査、現行 Lean の宣言を照合し、まず対象の最初の未完了な補題群について次の欄を埋めて統合担当と共有する。担当票の候補ファイルだけで編集権限が確定したとは扱わず、共有ファイルの編集担当と先行成果の受け渡し順も固定する。いずれかが確定できない場合は調査結果と未決事項を返し、推測した定理文や新しい `sorry` で実装を開始しない。

| 作業票の欄 | 必ず記録する内容 |
| --- | --- |
| 数学的仕様 | TeX ラベルと有効な本文、正確な Lean 定理文の型・量化順序・仮定・規格化・結論、原稿との差 |
| 入力と境界 | 対応する R 監査の結論、先行する検証済み宣言、外部入力の出典と未証明の範囲、担当ファイル・共有 API の編集担当者 |
| F01 の流用 | SpinGlass の対象コミット・ファイル・宣言と既存 `gaussianReal_stein` などの対応、流用する定義・証明と変更点、出典・ライセンス表示、Lean/mathlib の版差と移植後の検証。上流の証明を移植先の検証済み宣言と混同しない |
| 完了判定 | 変更ファイルの `lake env lean`、関連する最小 `lake build`、主要定理の `#print axioms` と定理文に残る仮定、原稿との照合、統合後の再検査、Blueprint 更新の引継ぎ |

`N` に依存して変わる確率空間上の分布収束と、概収束に必要な共通確率空間を定理文ごとに区別する。外部入力を仮定として受け取る定理では、条件付きの結論と入力自体の証明状態を別に報告する。

### モジュールと対応の確認

既存の雛形で採用している TeX のラベルに基づくファイル分け、`UpperCamelCase` のモジュール名、`SYK.CLT` 名前空間を維持する。README には実在するモジュールだけを掲載する。

- [x] `lemmas/` を `Lemmas/` へ改名し、すべての import を同時に更新した（旧段階6の完了記録）。
- [ ] W06 と各形式化単位で、関係するコメント・ドキュメント文字列が定理番号ではなく TeX のラベルを参照することを確認する。

各単位で個別 Lean 検査、関連する最小ビルド、主要定理の `#print axioms` と残る仮定の確認、原稿との対応を検査する。必要な Blueprint の編集細目は Chapters の計画で管理し、同じ単位内で完了する。Verso 休止中は本文と宣言参照の照合を行い、生成・参照検査は復帰後にまとめて行う。ワークスペース全体に影響する変更では `lake build` も実行する。既定ビルドから一時的に除外されている `Annealed_FE` と `Universality` は個別に検証済みとは扱わない。

検証時は対象コミット・差分、コマンド、結果、警告、未解決事項を記録する。担当票には現行の結論と次の作業を残し、詳しい完了記録は [作業履歴](../WORK_HISTORY.md) に移す。最終的には相対 CLT、標準化 CLT、対数 CLT の各宣言が、原稿の正確な主張・外部入力・残る仮定と対応し、仮置きの証明なしに検査されていることを確認する。大数則は F08 の仕様確定後に、その外部入力または内部証明の状態を別に記録する。

<a id="main-statements-2026-09-18"></a>

## 主結果の定理文（2026-09-18 の設定）

共同 CLT と二つの射影は `CLT/Main.lean` に定理文を持つが、証明は未完成で `sorryAx` に依存する。正確な型は Lean ソースと原稿で照合し、追加時の経緯は [作業履歴](../WORK_HISTORY.md#clt-main-statements) を参照する。

## Z01：複素平面上の零点のない領域

細目と進捗は [Model の Z01](../Model/EDITING_PLAN.md#z01) に集約する。CLT 側は必要な円板・帯状領域、一様性、内部証明か外部入力かの要件を供給する。領域が確定する前に、実逆温度の集中不等式や W06 の接続を待たせない。

全複素平面での非零性や複素逆温度の正値性は目標にしない。`Z z ≠ 0` を条件とする API と、その条件を供給する領域の定理を区別する。
