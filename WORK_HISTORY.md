# SYK の作業履歴

数学的な判断、重要な検査、現在の実装を理解するための不具合対処を記録する。旧パス・コマンド・未完了状態は当時の事実であり、現行手順は [README](README.md)、残件は [全体計画](EDITING_PLAN.md) を参照する。細かな作業票・差分・過去の文書は Git 履歴で確認できる。

この文書で「通常公理」は `[propext, Classical.choice, Quot.sound]` を指す。公理依存の確認と、定理文に残る外部入力の確認は別である。

<a id="blueprint-lint-2026-10-11"></a>

## Blueprint の警告の解消（2026-10-11）

`lake build SYKBlueprint` の警告 78 件を 2 件（依存パッケージ VersoBlueprint の universe 警告）にした。`Blueprint/SYKBlueprint/CLT.lean` に、`Model.lean`・`GaussianConcentration.lean` と同じ `set_option linter.mathlibStandardSet false` を加え、Verso の本文への書式 linter の警告 61 件を解消した。Verso の「宣言に docstring がない」警告 15 件は、`SYK.Params`・`SYK.MajoranaSystem`・`SYK.CLT.AnnealedInput` の各フィールドに docstring を加えて解消した（定理文・型・仮定は変えていない）。

検証：`lake build SYK` と `lake build SYKBlueprint` が成功し、警告は上の 2 件だけである。Blueprint の HTML を再生成し、`vbp check` は `ok=true`・`errors=[]` だった。HTML 生成時に `CLT.lean:25` の `$`q\ge4`` の数式変換に失敗する info が 1 件出る（本文の数式の書式で、今回の変更とは無関係）。

<a id="ring-cleanup-2026-10-11"></a>

## `ring` の `ring_nf` への退避の整理（2026-10-11）

`ring` が目標を閉じられず `ring_nf` に退避していた info 7 件（`gaussianReal_stein` の書き直しで消えた 13 件を除く）を整理した。`ring_nf` が目標を閉じる 1 件（`StandardGaussian`）は `ring_nf` に置換した。残りは、`ring_nf` の途中の正規形に後続のタクティクが依存していたので、置換せずに書き方を変えた。`Smooth`・`Lipschitz` の `exp (a) = exp (b) * exp (c)` の形の 4 件は `rw [← Real.exp_add]; congr 1; ring` とし、1 件は `mul_add`・`Real.exp_add` で展開してから `ring` とした。`Smooth` の回転の変数変換の 1 件は、`F` の引数を先に `rw [show …]` で書き換えて、不要な `ring` を 2 つ削除した。ゴールを変えていなかった 1 件の `ring` は削除した。

検証：`StandardGaussian`・`Smooth`・`Lipschitz` を `lake lean` で検査し、エラー・警告・info は 0 件だった。`lake build SYK` と `lake build SYKBlueprint` が成功した。`SYK.Probability.GaussianConcentration.*` の全宣言の名前・モジュール・型を変更の前後で書き出して比べ、一致した。主要定理は通常公理のみに依存する。

<a id="stein-proof-2026-10-11"></a>

## `gaussianReal_stein` の証明の書き直し（2026-10-11）

`StandardGaussian.lean` の一次元 Stein の恒等式 `gaussianReal_stein` の証明（約 350 行）を、mathlib の `integral_gaussianReal_eq_integral_smul`（密度による積分の表示）と `integral_mul_deriv_eq_deriv_mul_of_integrable`（`ℝ` 上の部分積分）を使う約 60 行の証明に置き換えた。`u = g`、`v = φ`（標準ガウス密度）とし、`φ' = -x φ` を使う。補助補題として、密度の微分 `hasDerivAt_gaussianPDFReal_zero_one` と、ガウス測度での可積分性を密度つきのルベーグ可積分性へ移す `integrable_gaussianPDFReal_mul` を private で加えた。可積分性は既存の `integrable_exp_abs_gaussianReal` から導くので、この補題を宣言を変えずに `gaussianReal_stein` の前へ移した。`set_option maxHeartbeats 400000` は不要になり削除した。`ring` が `ring_nf` に退避する info 13 件もこれで消えた。

検証：`StandardGaussian.lean` を `lake lean` で検査し、エラーと警告はなく、残る info は対象外の `ring` の 1 件だけだった。`lake build SYK` と `lake build SYKBlueprint` が成功した。`SYK.Probability.GaussianConcentration.*` の公開宣言（private を除く 641 行）の名前・モジュール・型を変更の前後で書き出し、完全に一致することを確認した。`gaussianReal_stein`・`pi_gaussian_stein_coord`・`log_partition_clt`・`standard_log_partition_clt`・`logPartition_hasSubgaussianMGF` は通常公理のみに依存する。

<a id="smooth-split-2026-10-11"></a>

## `Smooth.lean` の分割（2026-10-11）

`SYK/Probability/GaussianConcentration/Smooth.lean` は、共分散の補間による滑らかな場合の共分散評価と、多重指数のガウス・エルミート部分積分（`lem:Gaussian-Hermite-IBP`）を一つのファイルに連結していた。後者は前者の宣言を使わず、`StandardGaussian.lean` の `pi_gaussian_stein_coord` だけに依存する。そこで後者を `HermiteIBP.lean` へ移した。宣言の本文・名前・名前空間（`SYK.GaussianConcentration`）は変えていない。利用側は、共分散評価を使う `Lipschitz` が `Smooth` を、Hermite 部分積分を使う `GaussianChaos/CoefficientIBP` と `CLT/Chaos/PartitionDerivatives` が `HermiteIBP` を `import` する。`Smooth` の不要な Mathlib の `import` 16 件と、`HermiteIBP` の不要な `open scoped` も外した。

検証：元のファイルの前半・後半と、現在の `Smooth.lean`・`HermiteIBP.lean` を比べ、宣言の本文が一致し、差は `import`・`open`・冒頭の説明だけであることを確認した。変更した 5 ファイルを `lake lean` で個別に検査し、`lake build SYK` と `lake build SYKBlueprint` が成功した。`log_partition_clt`・`standard_log_partition_clt`・`logPartition_hasSubgaussianMGF`・`hermiteMulti_ibp_of_expGrowth`・`gaussian_cov_bound_smooth` は通常公理のみに依存する。Blueprint の HTML 生成と `vbp check` は実施していない（章の本文と参照する宣言は変更していない）。

<a id="lint-2026-10-10"></a>

## linter の警告の解消（2026-10-10）

`MAINT-LINT` を行った。まず、行列解析・CLT・Model の数ファイルの警告 12 件を直した。長い行の折り返し 9 件（`SingularValues`・`TraceExponential`・`PartitionDerivatives`）、`show` から `change` への置換 1 件（`TraceExpDerivatives`）、後続のタクティクが使う柔軟な `simp` の `simp only [...]` への固定 2 件（`PartitionSymmetry`・`Rademacher`）である。ビルドのログに出る `Try this` の提案は、複数の場所を同時に直すときに不完全なことがあった。そのため、提案は編集後の `lake env lean` で毎回確かめる。

`FiniteDimensionalGibbs` の `density_variance_nonneg` の未使用 `[DecidableEq d]`（1件）は、定理の仮定が減るので承認を待っている。

続いて `Lipschitz`（75件）を解消した。長い行 29 件の折り返し、`refine'` 18 件の `refine` への書き換え（解決される穴は `_` のまま、ゴールになる穴だけ `?_` にした）、柔軟な `simp`・`simp_all` 20 件の `only` への固定、未使用の引数 1 件、不要な `simpa` 1 件、`multiGoal` 5 件である。`multiGoal` は、後から `refine fun a => ...` で与えていた暗黙の関数（`integral_mono_of_nonneg` の `g`、`tendsto_integral_of_dominated_convergence` の `bound`）を、最初の `refine` の引数として渡すことで解消した。折り返しの検査は、`lake env lean` にも lakefile の `leanOptions`（linter の設定）を渡さないと警告が出ないので、`-Dweak.linter.mathlibStandardSet=true` などを明示して行った。

続いて `StandardGaussian`（257件）を解消した。長い行 129 件の折り返しと、長すぎるインラインの `by` ブロック 14 件の展開、`refine'` 58 件の `refine` への書き換え、柔軟な `simp`・`simp_all` の `only` への固定、未使用の引数 15 件の削除、`multiGoal` 16 件の解消である。`Integrable.mono'` の暗黙の関数 `g` は、後から `refine fun x => ...` で与えるのをやめて、`(g := ...)` として最初の `refine` に渡した。`by_cases ... <;> simp` の5箇所は、同じファイルの別の箇所と同じ `simpa [hj] using ...` の形に揃えた。`simp?` の提案は `<;>` で複数のゴールに適用されると分岐ごとに異なるので、両方の補題の和集合を使った。

`StandardGaussian` に残る3件は、承認が要る：`integrable_abs_coord_mul_exp_c_sum_abs_pi` の未使用 `[DecidableEq ι]`、`pi_gaussian_stein_coord` の未使用の仮定 `hc : 0 ≤ c`・`hC : 0 ≤ C`。

最後に `Smooth`（174件）を解消した。同じ方法で、長い行の折り返しと `by` ブロックの展開 160件ほど、`refine'` 41件の書き換え、柔軟な `simp`・`simp_all` 12件の固定、未使用の引数 13件の削除を行った。`multiGoal` は、`on_goal 1 => rw [...]` と `ring_nf` を `·` の中へ移す形で解消した。`refine'` の穴のうち、`norm_add_le`・`LinearIsometryEquiv.continuous`・`Real.abs_sin_le_one` などの引数は単一化で決まるので `_` のままにした。`?_` にすると、ゴールが増えるか、解けずに `whnf` の計算量の上限に達した。

残る警告 11 件は、未使用の仮定を外す変更なので、研究者の承認を得て解消した。

- 未使用の `[DecidableEq ι]`（`integrable_abs_coord_mul_exp_c_sum_abs_pi`・`euclidean_norm_le_sum_abs`・`hermite_product_exp_bound`・`integrable_of_euclidean_expBound`・`integrable_coord_mul_of_euclidean_expBound`）と `[DecidableEq d]`（`density_variance_nonneg`）を外した。後者は証明に `classical` を加えた。
- `pi_gaussian_stein_coord` と、それに仮定を渡すだけの `coord_stein_of_expGrowth` から、未使用の `hc : 0 ≤ c`・`hC : 0 ≤ C` を外した。論文の `lem:Gaussian-Hermite-IBP` に対応する `hermiteMulti_ibp_of_expGrowth`（`0 < C` を持つ）は変えていない。呼び出し側の `coord_stein_of_euclidean_expGrowth` は、この 2 つの仮定を自分の証明で使うので残している。
- `Smooth` の private 補題 3 件（`PolyFunction.deriv_closed`・`polyFunction_hermiteList`・`polyFunction_partialList`）の未使用の `[Fintype ι]` は、証明が使うので `[Finite ι]` に弱め、証明の中で `Fintype.ofFinite` を使う形にした。

以上で `MAINT-LINT` は完了し、linter の警告は 0 件である。ガウス基盤の保守計画（`GaussianConcentration/EDITING_PLAN.md`）は課題がなくなったので削除した。

検証：`lake build SYKBlueprint` が成功し、警告は 519 件から 0 件になった。Blueprint の生成と `vbp check` も成功した。変更前後の全 742 宣言を比べると、型が変わったのは上の仮定の削除だけで、名前・可視性・種類・モジュールは完全に一致する。主要 4 定理は通常公理のみに依存する。

<a id="clt-scope-fixed-2026-10-10"></a>

## 条件付き CLT の仕様確定（2026-10-10）

研究者の決定により、`AnnealedInput` を明示的に仮定する条件付き CLT と標準模型族への条件付き適用を確定仕様とし、凸収束補題の補完・外部入力の再調査・アニール入力の構築の3課題を計画から削除した。構造文書、CLT の案内と Blueprint の範囲説明も同期した。入力の構築とアニール命題自体は未形式化のままであり、課題の削除を証明の完了とは扱わない。数学の Lean 宣言・仮定・証明は変更していない。

検証：変更文書の相対リンク35件のファイル・アンカー、計画からの3課題の削除、廃止した節への参照が残っていないことを確認した。原稿の該当ラベルと Lean の明示的な入力も確認した。エージェント環境では elan 設定ファイルへの書込権限によりビルドできなかったが、その後、研究者が手元のターミナルで案内した検査を実施し、完了を報告した。`lake build SYKBlueprint`、Blueprint の CLT 章と両入口の Lean 検査、HTML 再生成、`vbp check` を完了し、`ok=true`・`errors=[]` を確認した（研究者の実行報告に基づく）。GitHub Actions の実行と Pages 公開の確認は、このローカル検証には含まない。

<a id="blueprint-workflow-split-2026-10-10"></a>

## 検証 CI と Pages 公開の分離（2026-10-10）

研究者の依頼により、下記の公開準備で統合した workflow を分離した。`lean_action_ci.yml` は `Lean Action CI` として数学・Blueprint のビルドと参照検査だけを行う。新設の `blueprint-pages.yml` は `Blueprint Pages` として独立に同じビルド・検査を行い、成功した HTML を公開する。Pages の操作と公開権限は公開 workflow にのみ置き、両者の concurrency group を分けた。検証 CI は古い実行をキャンセルし、公開 workflow は実行中の公開をキャンセルしない。公開手順と全体計画も分離後のファイル名に合わせた。

検証：両ファイルの build・生成・check のステップが文字列として一致すること、検証 CI に Pages 操作・書込権限がないこと、公開の main 条件2か所、build への依存、artifact パス、各 workflow 自身の起動条件、手動実行、更新文書の相対リンク先の存在をスクリプトで確認した。YAML 構文の parser による検査、Actions 実行、初回公開は未実施。数学・Blueprint の Lean ソースは変更していないため Lean の再検査は行っていない。公開完了は全体計画の `BLUEPRINT-PAGES` に引き続き残す。

<a id="blueprint-pages-preparation-2026-10-10"></a>

## GitHub Pages 公開の準備（2026-10-10）

公開依頼に基づき既存の `lean_action_ci.yml` を `Blueprint Pages` に拡張した。親ワークスペースでの数学・Blueprint ビルド、HTML 生成、`vbp check` を保持し、成功後に HTML のみを Pages artifact として転送する。公開は `main` に限定し、`pages: write` と `id-token: write` は後続の deploy job のみに付与した。Lake 設定・manifest・toolchain・workflow の変更も起動条件に加えた。操作手順は当時 `Blueprint/README.md` に置いた。その後、研究者向けの作業手順書として公開ファイルには含めない方針とした。数学のソース・主張・依存の版は変更していない。

検証：設定の処理順、公開条件、artifact のパスと GitHub 公式の Pages 権限要件を照合した。既存 HTML の `base` 要素を解決してローカル参照2309件のパス存在を確認し、欠落0件、ルート絶対パス0件だった。これは既存成果物のパス検査であり、新規生成・アンカー・検索の実動作の検査ではない。YAML parser は環境に存在せず構文の自動検査は未実施。Git は設定ファイルへのアクセスを拒否され、親 `AGENTS.md` も権限付きの再試行後に読めなかった。`lake`・`gh` は利用できず、Lean 再ビルド、Git の差分確認、GitHub 設定変更、push、Actions と公開 URL の検証は未実施。残件と完了条件は全体計画の `BLUEPRINT-PAGES` に記録した。

<a id="lake-lean-2026-10-11"></a>

## 個別検査のコマンドの整理（2026-10-11）

文書にあった個別検査のコマンド `lake env lean <file>` を `lake lean <file>` に改めた。`lake env lean` は環境変数を設定するだけで、依存をビルドせず、`lakefile.toml` の `leanOptions` も渡さない。このため、古い成果物による偽のエラーが出たり、linter の警告が出なかったりした。`lake lean` は依存を先にビルドし、そのファイルが属するライブラリの `leanOptions` を適用する。ワークスペースのライブラリに属さないファイルには、ルートパッケージの設定が使われる。全モジュールを import する補助スクリプトは、特定のファイルの検査ではないので、`lake env lean --stdin` のままにした。

実測：ワークスペースのルートから `lake lean` を実行すると、`SYK_CLT/SYK/...` のファイルにも 100 文字の linter が働いた。`lake env lean` では働かなかった。オプションの一覧を表示するファイルでは、`SYK_CLT/` で実行したときだけ `maxSynthPendingDepth=3` などが付いた。

<a id="repo-rename-2026-10-10"></a>

## リポジトリ名の変更（2026-10-10）

研究者が GitHub のリポジトリ名を `SYK` から `SYK_CLT` に変更し、ローカルのディレクトリも `SYK_CLT/` にした。Lake のパッケージ名 `SYK`・`SYKBlueprint`、Lean のライブラリ名、宣言の名前空間は変えていない。変わるのはディレクトリ名だけである。

ワークスペースのルートの `lakefile.toml` と `lake-manifest.json`（`SYK` と `SYKBlueprint` の `path`・`dir`）、雛形 `workspace/` の同じ 2 ファイル、CI（`actions/checkout` の `path` と雛形のコピー・生成のパス）、`workspace/README.md`、トピック別の説明 3 か所を `SYK_CLT` に合わせた。この文書より前の記述にある旧パスと旧コマンドは、当時の事実として残している。

検証：ワークスペースのルートからの `lake build SYKBlueprint` が再ビルドなしで成功した（約3秒）。

<a id="editor-root-2026-10-10"></a>

## エディタのプロジェクトルートと依存キャッシュの共有（2026-10-10）

VS Code の InfoView が動かない原因を調べた。Lean 拡張（v0.0.240）は、開いたファイルから親へたどり、最初に見つかった `lean-toolchain` のあるディレクトリをプロジェクトのルートとして `lake serve` を起動する。`SYK/lean-toolchain` があるので `SYK/` がルートとなり、親の共有キャッシュを使わず `SYK/.lake/packages` に mathlib 等のソース（692MB）を複製していた。`SYK/Blueprint/` は `lakefile.toml` はあるが `lean-toolchain` がないため、拡張がエラーを出してサーバーを起動しなかった。ワークスペースのルートからのビルドは、この間も共有キャッシュを使い、重複を作っていない。

研究者の承認のもとで、`SYK/lakefile.toml` と `SYK/Blueprint/lakefile.toml` に `packagesDir`（親の `.lake/packages`）を設定し、両方の `lake-manifest.json` の `packagesDir` を合わせた。`SYK/Blueprint/lean-toolchain` を追加した（ルートの規則が禁じる「明示的な指示なしの `lean-toolchain` の追加」に当たるので、承認を得た）。依存のリビジョンと Lean のバージョンは変えていない。

検証：`SYK/` と `SYK/Blueprint/` をそれぞれルートにして `lake env printenv LEAN_PATH`・`lake build` を実行し、依存が親の `.lake/packages` から解決され、複製も再ビルドも起きないことを確認した（約1秒）。ワークスペースのルートからの `lake build SYKBlueprint` も変更前と同じである。VS Code での InfoView の動作は、手元で確認する必要がある。

<a id="unused-declarations-2026-10-10"></a>

## 使われていない宣言の削除（2026-10-10）

`MAINT-UNUSED` の第3分類を処理した。研究者の方針は、Lean コードで使われておらず削除できる宣言は基本的に削除し、ライブラリを小さく保つことである。削除前のソースは `d5972da` にあり、以下の結果はそこから復元できる。

今でも数学的に有益で、必要になれば復元を検討するもの：

- **一次の Duhamel 公式**（`TraceExponential` の `Duhamel` 名前空間全体）。`fderiv_exp_apply` は、完備ノルム代数で `D exp(X)[V] = ∫₀¹ exp(sX) V exp((1-s)X) ds` を示していた。補助の `kernel`・`exp_sub_exp_eq_integral`・`continuous_duhamelIntegral`・`hasFDerivAt_exp`・`hasFDerivAt_exp_affine` も一緒に削除した。`normalizedTrace_duhamel_kernel` は、トレースの巡回性により `τ(exp(sA) B exp((1-s)A)) = τ(B exp A)` を示していた。これらは原稿の `eq:iterated-Duhamel-formula` の `k=1` の場合に当たる。ただし Lean の高階微分評価は冪級数と Schatten 評価を使うので、この経路を通らない。
- **ガウスの回転不変性の射影**（`Smooth` の `map_rotation_fst`）。`(μ⊗μ)` を回転して第1成分へ射影すると `μ` になる、つまり `cos θ·a + sin θ·b` が標準ガウスに従うことを示していた。同じ回転の測度保存は `rotation_measurePreserving` に残っている。
- **Schatten ノルムの反例**（`not_normalizedSchattenNorm_antitone`・`normalizedSchattenNorm_antitone_counterexample`・`normalizedSchattenNorm_diag_one_zero` と private の `diagOneZero` 系）。規格化 Schatten ノルムが `p` について減少するという以前の誤った主張を、`diag(1,0)` で否定していた。正しい単調増加は `normalizedSchattenNorm_monotone` にある。
- **抽象的な部分積分の枠組み**（`Smooth` の `IBPFamily`・`hermiteList_ibp`・`hermiteMulti_ibp`・`hermiteMulti_ibp_prod`）。仮の `Good` 述語を入力とする反復部分積分だった。具体的な仮定で述べる `hermiteMulti_ibp_of_expGrowth` に置き換わっていた。

途中段階として削除したもの：`coord_stein_of_manuscript_growth`（`hermiteMulti_ibp_of_expGrowth` の一次の場合）、`hermiteList_replicate`・`creation_hermite`、`gaussian_cov_sinH_intervalIntegrable`、`gradient_coord_eq`（`toLp` 版の `gradient_toLp_coord_eq_fderiv` が使われている）、`integrable_abs_mul_exp_abs_gaussianReal`、`Radial.hasFDerivAt_radial`（Euler の恒等式。原稿に対応する主張はない）、`normalizedTrace_mul_comm`（`normalizedTrace_duhamel_kernel` だけが使っていた）。

以前からどこにも使われていなかった private 宣言も削除した：`charpoly_exp_smul`・`roots_charpoly_exp_smul`・`charpoly_toEuclideanLin`・`exp_smul_posDef`・`charpoly_adjoint_comp_self_of_positive`・`trace_exp_re_pos`（`TraceExponential`）、`eigenvalues_eigenbasis_eq`・`eig_nonneg`（`SingularValues`）。モジュール機能を有効にしているため、private 宣言は import 側の環境に現れない。そこで、宣言のあるファイル内の出現で調べ、ドット記法で使われるものを除いた。

検証：`lake build SYKBlueprint` が成功し、警告は531件から519件に減った。Blueprint の生成と `vbp check` も成功した。変更前後の全宣言を比較し、残った759件は名前・可視性・種類・モジュール・型が完全に一致した。差は上の削除分（構造体の自動生成宣言を含む）だけである。主要定理は通常公理のみに依存する。孤立する宣言がなくなるまで、公開宣言の Lean の走査と private 宣言の検査を繰り返した。

### 参照のない小さな宣言の削除

研究者の判断で、参照がなく API として残す利益も小さい次の宣言を削除した。削除前のソースはコミット `89d0f69` にある。

今でも数学的に有益なもの：

- **一般の有限模型での奇数 Hermite 係数の消滅**（`CliffordSignParity` の `expectation_partitionFunction_mul_hermite_eq_zero`）。規格化しない `Tr exp(−βH(g))` と係数 `σ_N` を掛けない結合 `g` に対し、`N` が偶数で `α` が奇数なら `𝔼[Z·H_α]=0` を示していた。原稿の `lem: parity rule lemma` の `eq:odd-coefficient-zero` に当たるのは規格化した `Setting.Z` に対する `Setting.integral_Z_mul_hermite_eq_zero` で、CLT はそちらを使う。削除した版は同じ証明（頂点の符号反転 `hermiteMulti_vertex_flip` とゲージ不変性 `partitionFunction_sign_gauge`）の別の組み立てで、原稿に対応する主張はない。
- **規格化 Schatten ノルムの単調性と Gibbs 因子の厳密式**（`normalizedSchattenNorm_monotone`・`powerMean_mono`、`normalizedSchattenNorm_exp_hermitian`）。前者は規格化 Schatten ノルムが `p` について非減少であること（冪平均の不等式）、後者は `‖exp(−tβH)‖_{1/t} = (tr exp(−βH))^t` である。CLT の高階微分評価は冪級数と語の評価を使うので通らない。
- **ゼロ Lipschitz 定数の裾**（`product_standardGaussian_upper_tail_zero`・`product_standardGaussian_lower_tail_zero`、`logPartition_upper_tail_of_beta_zero`・`logPartition_lower_tail_of_beta_zero`）。Lipschitz 定数が 0 なら、正の偏差の事象の確率は 0 であることを示していた。`β = 0` の中心化と両側の裾の主張は `logPartition_centered_of_beta_zero` などに残る。

そのほかに削除したもの：`gibbsState` とその `gibbsState_eq_expectation_thermalDensity`・`realLogPartitionFunction`（`FiniteDimensionalGibbs`）、`expectation_eq_ofReal_re`、`normalizedTrace_add`・`normalizedTrace_zero`、`Schatten.normalizedNorm_nonneg`、`polynomial_eval_mem_hermite_span` と補助の `polynomialEvalLinear`、`iterDirectionalFDeriv_traceExp_bound_of_norm_le_one`、private の `sum_sv_exp`・`sum_eigenvalues_exp_smul`・`singularValues_fin_of_positive`。

走査は `rfl` で閉じる補題の `simp`・`dsimp` 経由の使用を検出できない。実際に `gaussianCouplings_eq_pi` と `matrixTraceCLM_apply` は走査で未使用と判定されたが、`simp only` が使っていたため、削除をやめて残した。この 2 件は、使われているので削除しない。

検証：`lake build SYKBlueprint` が成功し、警告は 519 件のまま変わらない。Blueprint の生成と `vbp check` も成功した。変更前後の全宣言の比較で、残った 742 件は型を含めて一致し、差は上の 17 件の削除だけである。主要定理は通常公理のみに依存する。

<a id="matrix-namespace-2026-10-10"></a>

## 行列解析の副名前空間の廃止（2026-10-10）

`MAINT-NAMESPACE` と `MAINT-ROOT` を行った。`SYK.MatrixAnalysis.Matrix`（53件）と `SYK.MatrixAnalysis.LinearMap`（7件）の宣言を `SYK.MatrixAnalysis` の直下へ移した。mathlib の `Matrix`・`LinearMap` と同名の副名前空間があると、宣言を誤認しやすく、`open _root_.Matrix` も必要になっていたためである。`normalizedTrace` は改名せず、Model の `SYK.normalizedTrace` とは別の定義であることを docstring に書いた。

`_root_` を使っていた2件は通常の位置で宣言した。

- `trace_exp_smul_of_isHermitian` は `ExpAux` の外へ出した。
- `contDiff_traceExp` は、`DerivAux` の private な局所インスタンス3つと一緒に `section RealScalars` に置いた。インスタンスの適用範囲は変更前と同じで、後続の定理文には及ばない。

旧名前空間の区画は名前のない `section` に置き換え、`variable` の適用範囲を保った。外部の利用箇所は `CLT/Chaos/PartitionDerivatives.lean` と `PartitionHigherDerivatives.lean` だけだった。

検証：`lake build SYKBlueprint` が成功し、警告は531件で変更前と同数だった。Blueprint の生成と `vbp check` も成功した。変更前後の全798宣言を、改名の対応を当てはめて比較し、名前・可視性・種類・モジュール・型が完全に一致した。主要定理（`log_partition_clt`・`standard_log_partition_clt`・`standard_partition_clt`・`logPartition_hasSubgaussianMGF`）は通常公理のみに依存する。

<a id="docs-cleanup-2026-10-10"></a>

## 文書の整理（2026-10-10）

全体計画にあった手順（原稿の改訂と実装の同期、共同作業と別環境への引き継ぎ、Blueprint の更新の規則）を `AGENTS.md` へ移し、CLT の構造文書から履歴の記述とエージェントへの指示を除いた。補題の索引は各モジュールの docstring に一本化し、構造文書には探し方の案内だけを残した。話題別の README（CLT・SuperConcentration・`workspace/`）から日本語の内部文書へのリンクを外し、定理文の所在と公理依存を英語で書いた。CLT とガウス基盤の `AGENTS.md` は、Model・SuperConcentration と同じ簡潔な形にそろえた。日本語の文書は、名詞の連なりと長い文を開いて読みやすくした。規則の効力と数学の内容は変えていない。

検証：Lean の変更は docstring のコメントだけで、11ファイルの個別検査と `lake build SYK` が成功した（警告531件、変更前と同数）。主要10定理（CLT 6、集中評価 4）は通常公理のみ。全 `.md` の相対リンクと見出しアンカーの検査で不備は0件だった。ルートの `README.md` は人間が管理するので編集しておらず、28行目に日本語の構造文書へのリンクが残る。

<a id="gaussian-maintenance-2026-10-10"></a>

## ガウス基盤の探索タクティク・非推奨 API の整理（2026-10-10）

`Probability/GaussianConcentration/` の `aesop`・`grind` 12か所（`grind +suggestions` を含む）を、ゴールを確認したうえで明示的な証明に置き換えた。符号反転不変性は mathlib の `gaussianReal_map_neg`、台の包含は `Function.support_mul_subset_left`、`L.toNNReal` は `Real.coe_toNNReal'` を使い、`Function.update` の計算と直積集合の等式は場合分けで示した。`pi_gaussian_stein_coord` の外側の3つの `have h_split` は、最後の合成で参照するため `h_slice`・`h_lhs`・`h_rhs` と名付けた。

非推奨 API 8件（`integral_finset_sum`、`ContinuousMultilinearMap.sum_apply`・`smul_apply`、`ContinuousLinearMap.smul_apply`、非推奨の import 2件）を新しい名前に直した。`maxHeartbeats` は、`Smooth` の引き上げを削除し、`gaussianReal_stein` は 4000000 から 400000（既定値の2倍）に下げて理由のコメントを付けた。

検証：`lake build SYK` が成功し、警告は541件から531件に減った（非推奨8件と `maxHeartbeats` の2件）。変更前後の全宣言の型・可視性・モジュールは完全に一致した。主要定理は通常公理のみ。書式の警告は残っている。

<a id="aux-names-2026-10-10"></a>

## 公開のまま残る `*Aux` 名の整理（2026-10-10）

`SingularAux` の公開補題8件を `SYK.MatrixAnalysis.LinearMap`（線形写像の特異値・Schatten の補題）へ、行列についての `toEuclideanLin_conj_diagonal_apply` と `ExpAux.trace_exp`（`trace_exp_smul_of_isHermitian` に改名）を `SYK.MatrixAnalysis.Matrix` へ移した。`SVDAux.sv` と、その型に現れる3補題（`normalizedSchattenNorm_eq_sum`・`sum_sv_conjDiag`・`sum_sv_rpow_nonneg`）はファイル内でしか使われないので `private` にした。`TraceExpDerivatives` で重複していた2つの `NormedSpace ℝ (Matrix n n 𝕜)` の局所インスタンスは、名前付きの `Matrix.realNormedSpace` 1つにまとめた。

検証：`lake build SYK`（警告541件、変更前と同数）が成功した。変更前後の全宣言を、改名の対応を当てはめて比較し、型が一致した（インスタンスの名前の差を除く）。公開から private への変更は上の5件（自動生成の `congr_simp` を含む）だけだった。

<a id="instance-consolidation-2026-10-10"></a>

## 確率測度インスタンスの集約（2026-10-10）

CLT の16ファイルに重複していた `IsProbabilityMeasure` の局所インスタンス（`standardGaussianMeasure` 版・`gaussianCouplings` 版、計20個）と `PolynomialDensity` の `letI` 2か所を削除し、定義の隣に大域インスタンス `standardGaussianMeasure_isProbability`（`Model/GaussianDisorder`）と `SYK.GaussianChaos.gaussianCouplings_isProbability`（`Probability/GaussianChaos/Basic`）を1つずつ置いた。`Prop` の型クラスなので他のインスタンスとは衝突しない。

検証：`lake build SYK`（警告541件、変更前と同数）が成功した。変更前後の全宣言を比較し、差は追加した2件と、削除した局所インスタンスの自動生成名だけで、他の宣言の型は変わっていない。主要定理は通常公理のみ。

<a id="blueprint-package-2026-10-09"></a>

## Blueprint の独立パッケージ化（2026-10-09）

Kamijima の承認した計画に基づき、Claude が実施した。Blueprint を、リポジトリ内の独立した Lake パッケージ `SYKBlueprint`（`Blueprint/`）にした。モジュール名は `Blueprint.*` から `SYKBlueprint.*` へ変えた。配置は Verso Blueprint の雛形と参照例（`FLTBlueprint` など）に合わせ、文書の最上位 `SYKBlueprint.lean`、生成入口 `SYKBlueprintMain.lean`（`vbp build` が `{パッケージ名}Main.lean` を探す）、章 `SYKBlueprint/*.lean` とした。パッケージは自身の `lakefile.toml`（`SYK` へのパス依存、Verso Blueprint v4.32.0、`needs = ["SYK/SYK:leanArts"]`）と `lake-manifest.json`（親と同じリビジョン）を持つ。

親ワークスペースの `lakefile.toml` は `SYK` と `SYKBlueprint` の `require` だけを持ち、独自のターゲットも既定対象も持たない。そのため全体の検査は `lake build SYKBlueprint` と明示する（CI は `build-args: SYKBlueprint`）。`lake update SYKBlueprint` はネットワークを使わずに完了し、全パッケージのリビジョンは変更前と一致した。親の雛形（`workspace/`）、ルートの `AGENTS.md`、各 README・`AGENTS.md`・CI の生成パスを合わせて更新した。

検証：`lake build SYK`、`lake build SYKBlueprint`、HTML 生成と `vbp check`（`errors=[]`、`ok=true`）が成功した。`SYK/Blueprint/.lake/packages` は作られず、依存の取得は親の `.lake/packages` に共有されている。GitHub 上の CI と、リポジトリ単体（親の雛形なし）での `Blueprint/` のビルドは未確認である。ルートの `AGENTS.md` の全体ビルドの記述は、親に既定対象がなくなったため、各プロジェクトの規則が定める対象を実行する書き方に改めた。

<a id="import-cleanup-2026-10-09"></a>

## import の整理と公開前の文書修正（2026-10-09）

Kamijima の承認した方針で Claude が実施した。定理文・証明本体は変えていない。

- import：宣言レベルの参照から、各モジュールが実際に使う SYK モジュールを求めた。使っていない import を外し、外したことで届かなくなった依存だけを直接 import に足した（11モジュール）。実際に使っている既存の import は残した。import の最長の鎖は22段から17段になった。
- 冒頭の説明がなかった6モジュール（`Model` の3つ、`StandardGaussian`、`SecondChaosAsymptotic`、`GaussianQuadraticCLT`）に英語のモジュール docstring を追加した。
- 古い記述の修正：旧作業ID（F02・F04・F05・W06・Z01）、存在しない `ModelParameters`、公開用 README の「Codex」、未参照のアンカーを直した。前回の記録にあった「CI は Lean 以外の変更でも起動する」は実際の設定と合っていなかったので、実際の起動条件（main への push で `**.lean` が変わったとき）に訂正した。CI の設定自体は変えていない。

検証：`lake build SYK`（警告541件、変更前と同数）、親の `lake build`、HTML 生成と `vbp check`（`errors=[]`）が成功した。変更前後の全宣言の型を比較し、差は `local instance` の自動生成名の番号の振り直しだけだった。

<a id="gaussian-ibp-removal-2026-10-08"></a>

## 未使用の `GaussianIBP.lean` の削除（2026-10-08）

`SYK/Probability/GaussianIBP.lean`（6589行）を削除した。どのモジュールからも import されず、Blueprint も import するだけで宣言を参照していなかった。一次元の Stein の補題と有限次元 Hilbert 空間上の共分散つき部分積分を含んでいた（冒頭の説明と名前空間 `PhysLean.Probability.GaussianIBP` が PhysLean の同名ファイルを参照していたが、由来とライセンスは未確認）。SYK の証明が使う指数増大つきの標準ガウス・多重指数 Hermite の部分積分は共有 `GaussianConcentration` が与えており、分配関数 `Z_N` は多項式増大の仮定を満たさないため、このファイルでは置き換えられない（前者は任意分散・多項式増大・一次のみ、後者は分散1・指数増大・高階）。警告74件と、`mathlib` の `ProbabilityTheory` 名前空間への宣言追加も解消した。必要なら `git show 3f36dc9:SYK/Probability/GaussianIBP.lean` で取り出せる。

<a id="api-naming-2026-10-08"></a>

## 公開前の名前空間・モジュール名の整理（2026-10-08）

Kamijima の承認した計画に基づき、Claude が実施した。開始リビジョンは `3f36dc9`。リポジトリの公開に備え、宣言の名前空間・モジュールのパス・可視性だけを変え、定理文の数学的内容は変えていない。互換用の別名や旧パスは作っていない。

- モジュールの改名：`Analysis/Matrix/TraceExponential`、`Probability/GaussianChaos/{Basic,CoefficientIBP,Orthogonality,HermiteDensity,PolynomialDensity}`、`CLT/Log/{Taylor,EventBound,Asymptotics}`。汎用補題の `LpDistributionTransfer` は `Probability/` へ移し、CLT への import を mathlib の1モジュールに置き換えた。docstring の「`L¹` or `L²`」の脱字も直した。
- 名前空間：ガウスカオス層を `SYK.GaussianChaos`、`Probability/` 直下を `SYK.Probability`、凸関数列を `SYK.Analysis`、行列解析を `SYK.MatrixAnalysis`（`SingularAux`・`ExpAux`・`SVDAux` はその下）へ移した。対応は [AGENTS.md](AGENTS.md#公開-api-の変更) に記す。
- 他のモジュールから使われず、公開のまま残す宣言の型にも現れない `*Aux` の補題63件を `private` にした（自動生成の `congr_simp` 2件も伴って private になった）。`DerivAux.contDiff_tE` は `SYK.MatrixAnalysis.Matrix.contDiff_traceExp`、`iteratedFDeriv_tE_bound_hermitian` は private の `iteratedFDeriv_traceExp_bound_hermitian` に改名した。
- Blueprint の宣言参照と import、CLT の ARCHITECTURE・README、関係する docstring を更新した。

検証：変更前後の全1258宣言を名前の対応に沿って比較し、型が文字列として一致した。公開から private への変更は上記の65件だけだった。`lake build SYK`（警告615件、変更前と同数）、親の `lake build`、HTML 生成と `vbp check`（`errors=[]`）が成功した。抽象・標準模型の CLT、`Setting.integral_log_Y_isBigO`、集中評価の裾と MGF、行列微分評価、Hermite 完全性などの主要定理は通常公理のみで、変更前と一致した。`hFE : AnnealedInput` は引き続き明示的な仮定である。

文脈を引き継がない読み取り専用のサブエージェントが、変更前の記録から名前の対応と private 化の規則を独自に再計算して監査した。型・可視性・差分の範囲・公理依存・ビルドに問題はなかった。ARCHITECTURE の旧モジュール名1件、名前空間の表の不足1件、AGENTS.md の文言（自動生成補題の扱い）1件の指摘を反映した。

残した課題：公開のまま残る `*Aux` 名、どこからも使われない公開補題、import の鎖の解消、局所インスタンスの集約、文書の役割の再配置、LICENSE、リポジトリ名の変更。旧モジュール名の olean がローカルキャッシュに残るため、キャッシュのない環境（CI など）でのビルド確認が望ましい。コミットは作成していない。

<a id="repo-layout-2026-10-07"></a>

## 数学パッケージと文書の配置変更（2026-10-07）

Kamijima が担当・統合し、承認済みの構成変更を実施した。数学を `SYK/{Analysis,Probability,Model,SuperConcentration,CLT}/`、論文を `Paper/`、ノートを `Notes/`、4章と本文・生成入口を `Blueprint/` に集約した。旧 `Preliminaries` は `PartitionSymmetry` とした。独立した Rademacher 模型の `Annealed_FE` と対応章、旧設計資料を削除し、ガウス模型の `AnnealedInput` の説明を CLT 章へ移した。

子パッケージ名 `SYK` と公開宣言の名前・型・仮定・規格化・属性を保持した。子は mathlib、親 `ResearchWorkspace` はローカル SYK と Verso Blueprint に依存する。親の既定 `Blueprint` は `needs = ["SYK/SYK:leanArts"]` で数学全体も検査する。依存のリビジョンを保持し、CI は生成入口と論文のパスだけを変更した。

数学52ファイルと Blueprint の6ファイルの個別 `lake env lean`、`lake build SYK`、親の `lake build` は成功した。主要25宣言の `#print`・`#print axioms` は開始版と一致し、通常公理のみだった。数学本文は承認した import・参照コメントの置換以外不変、論文5 TeX と Notes の TeX・追跡 PDF はバイト一致した。

`lake lean SYK/Blueprint/Build.lean -- --run SYK/Blueprint/Build.lean --output SYK/_out/site --pdf` と `lake exe vbp check --site SYK/_out/site` は成功し、参照検査は `errors=[]`・`ok=true` だった。論文全体・4単独節・Notes の `latexmk` 検査も成功した。全体論文は警告なし、単独節には他節の参照・引用警告、Notes と任意 PDF には組版警告が残る。数学の既存 linter・非推奨警告と Blueprint の書式・依存側 universe 警告も残る。`sorry` 警告はなかったが、ガウス CLT の `hFE : AnnealedInput` は未構築の入力である。更新後の GitHub CI は未実行で、設定と対応するローカルコマンドを確認した。構成変更の独立した監査は実施していない。

<a id="verso-restore-2026-10-07"></a>

## Verso の検証復帰（2026-10-07）

Kamijima が担当・統合した。保存した Verso Blueprint `v4.32.0` と依存リビジョンを復帰し、章のビルド、HTML 生成、`vbp check`、CI の生成・参照検査を有効にした。CI の起動条件（main への push で `**.lean` が変わったとき）は変えていない。

任意 PDF の検査は、章の表示数式終端に残る `$$`、旧 `\rm`、余分な inline `$` で失敗した。旧 `Chapters/AnnealedFE.lean` と `Chapters/CLT.lean` の表示構文だけを直し、数式内容・宣言参照・証明状態を保った。

全5章・本文・生成入口の個別 Lean 検査と最終 `lake build` が成功した。旧入口 `lake lean SYK/BlueprintMain.lean -- --run SYK/BlueprintMain.lean --output SYK/_out/site`、`lake exe vbp check --site SYK/_out/site` と任意 PDF も成功した。主要25宣言の型・定義・公理出力は前回と一致した。抽象・標準模型の CLT は通常公理のみで `hFE` を仮定し、当時の Annealed_FE 章が参照する2主定理は既存の `sorryAx` に依存していた。生成成功をその証明完成と扱っていない。この独立模型は後の配置変更で削除した。

既存の linter・書式・universe・組版警告が残った。読み取り監査後に統合を完了した。GitHub 上の更新後 CI は未確認であり、ローカルコマンドの成功とは区別した。

<a id="clt-cleanup-2026-10-06"></a>

## 証明の共有と読解案内の整理（2026-10-06–07）

Kamijima が担当・統合した。特異値の平方・単調性は mathlib の補題、有限和 Hölder は非負実数の有限和不等式と正の `1/r` 乗を使う証明に整理した。零を許す列と `0<r` の仮定を保持した。短縮案では `0<r` が未使用になったため、仮定の数学的役割が見える後者の証明を採用した。

`Main` は分配 CLT を先に証明し、結合定理が下位の対数 CLT と共通半径で結び、個別対数 CLT は射影する構造にした。二次観測量の可測性2補題と Hermite2 評価を実際の利用側で共有した。四次モーメントは各項の可積分性を確認して有限和を積分する。行列トレース指数は `MatrixAnalysis.Matrix.traceExp` に集約し、`DerivAux.contDiff_tE` と `iteratedFDeriv_tE_bound_hermitian` の公開名を保った。

変更・直接利用側の15ファイルの `lake env lean` と、当時の **`lake build CLT`** が成功した。開始時の主要22宣言は、行列微分2補題の承認済み定義置換を除き型・定義が一致した。両定義の展開式の一致は `rfl` でも検査した。共有補題を含む25宣言の公理依存は通常公理のみだった。論文5ファイルは開始版と一致し、温度 `0<|β|<βq`、尺度 `N^(q/2-1)`、分散 `(q!/2)β²(ℓ_q'(β))²` と標準化分散1を保持した。既存警告の内訳は変わらず、読み取り監査後に統合した。`hFE` は明示的な仮定として残る。

<a id="clt-refactor-2026-10-06"></a>

## 有限補題と漸近 CLT の分離（2026-10-06）

Kamijima が担当・統合した。汎用 Hermite 積と測度対称性を `GaussianHermiteBasic`、有限のガウス変数二乗の観測量と法則対応を `GaussianQuadraticObservable` に移した。これにより Hermite 展開から模型固有の符号ゲージ、四次モーメントから二次 CLT・係数漸近への依存を除いた。

有限行列解析の実際の外部利用は `PartitionDerivatives` だけだったため Model への先行移設を採用しなかった。2種類の規格化トレースは、`ℂ` と一般 `RCLike`、非空型の仮定、定義式が異なるため保った。移設12公開宣言の型・定義と証明ブロック・属性を比較し、名前・規格化を保持した。

新規・変更・直接利用側の13ファイルの個別検査と `lake build CLT` が成功した。主要24宣言の公理依存は通常公理のみ。原稿の温度・尺度・分散・残る `hFE` を照合し、読み取り監査後に統合した。

<a id="clt-log-apply-completion-2026-10-05"></a>

## 対数の期待誤差と標準模型族（2026-10-05–06）

Noda が担当・統合した。`Setting.cubed_scale_Y_lt_half_bounded` と `Setting.integral_log_Y_isBigO` により、`a=q/2-1`、非零の小さい固定実逆温度で `N^(3a) P(Y_N<1/2)` の終局的有界性と `E[log Y_N]=O(N^(-2a))` を証明した。二次・四次モーメント、高次剰余、分散漸近、`Z_N≥1` と `log E Z_N=O(N)` を使い、分布収束からモーメントを推論していない。自然数べきの逆数による指数は偶数 `q≥4` で原稿と一致し、温度についての定数の一様性は主張しない。

`StandardModel.lean` は `N n=q+2*n`、標準表現の模型族を構成し、全偶数 `N≥q` との一意な対応と `2^(-N/2) Tr` の規格化を接続した。3つの公開定理はその族に対する `AnnealedInput` を仮定し、相対・標準化・対数 CLT を適用する。標準表現を抽象 `Main` の証明依存へ追加していない。

初回は指定環境・依存成果物がなく検査できなかった。環境更新後、Lean 4.32.2（Windows）で必要な依存をビルドし、実数指数と自然数指数の変換、確率測度のインスタンスと依存型を修正した。`lake env lean SYK/CLT/Lemmas/LogAsymptotics.lean`、`SYK/CLT/StandardModel.lean`、`SYK/CLT/Main.lean` と `lake build CLT` が成功した。新規8宣言と結合 CLT の公理依存は通常公理のみで、型・仮定・原稿のラベルを照合した。変更モジュールに新規警告はなく、上流の既存警告は残った。Blueprint の93宣言を `#check` し、本文と依存を更新した。命題自体・入力構築・表現独立性は成果に含めない。

<a id="clt-input-2026-10-04"></a>

## アニール入力の整理（2026-10-04）

Kamijima が担当・統合した。開始版 `f87e0a064cd527bd58f7354eed32c83cbd33cfee` の原稿 `prop:annealed-free-energy` と照合し、`AnnealedInput q S` から旧証明本文の追加6評価フィールドを削除した。残る内容は `ℓ`、偶性・凸性・`C¹` 正則性、圧力と導関数の全実軸での局所一様収束、非零の逆温度での `βℓ_q'(β)>0` である。削除した評価を別の仮定として残していない。

`Setting` と3主定理の結論、有限モーメント・高次剰余、尺度・温度・中心化・分散を保持した。`Basic` と直接利用側の個別検査、`lake build CLT`、主要型・公理依存の確認が成功した。主 CLT は通常公理のみだが、一つの一般表現族 `S` に対し命題文の内容を仮定する。原稿の標準模型族についての命題や、一般表現への外部極限定理の適用可能性を証明したとは扱わない。

<a id="clt-audit-2026-10-04"></a>

## 現行原稿全体との照合（2026-10-04）

`6b36c7c96be98f81f49f82a03b8189ae51a5ca76` の原稿全4節を、研究者の指定に従い赤字を採用案として照合した。温度・中心化・規格化・尺度・分散・剰余の次数は維持されていた。一般の符号付き置換と Duhamel 積分表示は、Lean の個別対称性・高階微分評価と同一視しない。凸収束の Lean 定理は関数の局所一様収束を仮定するため、各点収束からの導出は未形式化のままだった。

原稿5ファイルと数学の証明項を保ち、説明を同期した。関係11ファイルの個別検査、`lake build CLT`、主要9宣言の公理確認と章参照85宣言の `#check` は成功した。主結果は通常公理のみで当時の追加6フィールドを含む `AnnealedInput` を仮定していた。これは後続の入力整理で解消した。

一時出力の論文全体 `latexmk` は成功し、赤青併記では参照が解決した。赤字だけを採用する読み方では `eq:even-multi-index` の参照1件が未解決になり、原稿担当へ修正を委ねた。引用原文の再監査とアニール命題の証明は行っていない。

<a id="z01-local-zero-free-2026-09-28"></a>

## 固定有限行列の局所非零円板（2026-09-28–29）

現行 CLT が複素対数や `N`・標本一様の非零領域を必要としないことを確認し、研究者は固定 `H` の局所円板を選択した。非空有限次元の自己共役行列と各実 `β` について、連続性から半径 `ε(H,β)>0` の複素円板で `Re Z_H(z)>0`、非零性、主値 `Complex.log ∘ Z_H` の正則性を証明した。外部結果・ノルム上界を追加せず、半径の一様性や複素平面全体の非零性は主張していない。

`lake -f SYK/workspace/lakefile.toml env lean SYK/Model/FiniteDimensionalGibbs.lean`、同設定の `build Model SuperConcentration CLT` と既定ビルドが成功し、5新定理は通常公理のみだった。9月29日の統合後の `lake build` も成功した。

<a id="clt-integration-audit-2026-09-29"></a>
<a id="clt-nonzero-temperature-2026-09-28"></a>
<a id="clt-r-f-completion-2026-09-28"></a>

## 条件付き CLT の統合と温度・外部入力の判断（2026-09-28–29）

F03 の Rademacher 評価、F04 の任意階微分、F05 の高次剰余を統合した。F06 は二次係数の漸近、ガウス変数二乗和の CLT、残差の `L²` 消失と有限サイズ分散の正値性から相対・標準化 CLT を証明した。F07 は一様四次モーメント、小確率事象、`Z_N≥1` と対数の局所近似により中心化誤差の尺度付き `L¹` 消失と対数 CLT を証明し、共同定理の `sorry` を除去した。

`lake env lean SYK/CLT/Lemmas/LogAsymptotics.lean`、`lake build SYK.CLT.Main`、`lake build CLT`、既定ビルドが成功し、主要4 CLT の公理依存は通常公理のみだった。初期の相対・対数 CLT は逆温度ゼロの退化例も含んでいたが、研究者の指示で主・中間 CLT をすべて `0<|β|<βq` に統一した。零分散で標準化できない点を原稿と照合し、有限模型の逆温度ゼロでの恒等式と全実軸の解析・係数評価は保持した。変更後の `lake -f SYK/workspace/lakefile.toml build CLT` と主要8 CLT の公理確認も成功した。

R04-A では標本ごとの概収束の記述を除き、当時の `thm: input` を期待クエンチ・アニール圧力の決定論的共通極限へ修正した。F08 は概収束の形式化対象がなくなり、新規 Lean 宣言なしで仕様確定を完了した。その後の現行原稿はアニール圧力の極限と極限関数の微分可能性だけを述べる。いずれの段階も `AnnealedInput` の構築や外部定理自体の Lean 証明を意味しない。原稿の `latexmk` 検査は成功し、当時の最終ログに未解決引用・参照や組版警告はなかった。

9月29日に統合版 `c20e415` を `lake -f SYK/workspace/lakefile.toml build CLT` と既定ビルドで再検査した。主要 CLT は通常公理のみで、実温度、尺度、極限分散、3つの結論と共通半径を原稿に照合した。既存の linter・非推奨警告と明示的な `hFE` は残った。

<a id="clt-abstract-input-2026-09-27"></a>

## 有限模型と抽象入力の分離（2026-09-27）

有限模型を `FiniteModel.lean` に分離し、一般の `Params` と非空有限行列表現のモーメントを証明した。標準表現との規格化照合は `Normalization.lean` へ移し、抽象 `Main` の依存から外した。3主定理の入力を `{q : ℕ} (S : Setting q) (hFE : AnnealedInput q S)` にそろえ、`S` と重複する偶数性・`4 ≤ q` の引数を除いた。全フィールド・結論・規格化を保持した。

個別検査と `lake -f lakefile.toml build CLT` は成功した。初回の共有キャッシュの権限不足・成果物欠落は権限付き再実行と必要依存の再構築で解消した。有限模型と入力からの漸近結果は通常公理のみだったが、当時の最終 CLT には既存 `sorryAx` が残った。相対・対数ゆらぎの逆温度ゼロを除いた改訂中の原稿との差を当時は明示し、後続の統一で解消した。

<a id="clt-r01-r05-audit-2026-09-27"></a>

## 原稿と引用元の数学的監査（2026-09-27）

[He2026 v3](https://arxiv.org/abs/2607.18998v3) の Theorem 1.1、Theorem 2.5、Proposition 3.3 を原文照合した。ハミルトニアンの変換 `H̃_N=2^(-q/2)H_N`、`s=2^(q/2)|β|`、規格化トレース、正の Lehmann 表現、二次モーメント `2^(2-q)s²`、圧力微分公式を確認した。He の固定した正の逆温度における期待クエンチ・アニール圧力の極限は、全実軸の標本ごとの概収束を直接裏付けない。[GPSZ2026 v1](https://arxiv.org/abs/2605.02768v1) もその主張をそのまま供給しなかった。負の逆温度でのガウス対称性・逆温度ゼロ・原稿内の正則性導出を引用と区別した。

Hermite の規格化、`η≤α` の成長仮定、Duhamel と規格化 Schatten Hölder、Rademacher 符号化、Newton/Hoeffding を照合した。高階微分の `r!` と単体体積 `1/r!` は相殺する。対角二次係数の同一性はサイト置換・ガウス符号対称性によるもので、原稿に理由を補った。凸性による各点収束からの局所一様収束は非形式的に確認したが、その段階で Lean 証明済みとは扱っていない。

`E(g²-1)²=2`、`E(g²-1)⁴=60` から規格化和の四次モーメント `3+12/M_N≤15` を得る対数誤差の議論を明記した。`P(Y_N<1/2)=O(N^(-3a))` と `Z_N≥1` による二事象分割は `-E log Y_N=O(N^(-2a))` を与える。原稿の軽微な誤記修正後、`latexmk` は警告・未解決参照なしで成功した。

<a id="clt-f02-completion"></a>

## 一次・二次カオスの同定（2026-09-27）

符号付き頂点転置と固定濃度集合の推移性から対角係数の同一性を証明した。一次微分の指数評価、ガウス部分積分、放射方向微分、局所的な可積分支配による期待値との微分交換を接続し、全実 `β` で一次射影零と二次射影を同定した。係数 `1/(2M_N)`、`H₂(x)=x²-1`、分散1の測度、実表現次元の規格化を照合し、標準表現やアニール入力を追加要求しなかった。

当時の5ファイルの個別検査と `lake -f lakefile.toml --old build CLT` は成功し、主要8定理は通常公理のみ。既定ビルドも成功したが、その環境の対象は別研究の `RSATMain` であり、配布設定全体の検証と同一視していない。最終 CLT は当時まだ未完成だった。

<a id="clt-f01-completion-2026-09-27"></a>

## ガウス部分積分と `L²` 完全性（2026-09-26–27）

一般のガウス–エルミート部分積分を共有 `Smooth.lean` に置いた。仮定は `C^{|α|}` と各 `η≤α` の偏導関数のユークリッドノルムに関する指数増大で、仮の `IBPFamily`・`ExpIBPChain` や余分な正則性を公開入力に残していない。空の有限型と `α=0` も扱い、両辺の可積分性を証明した。`Z_N` への適用は当時の F04 に分けた。

SpinGlass `dc1d3820af6e443c09bd1177ec3e409cf0640d5c` の指数増大・Stein 補題を流用候補として調べた。先方は Lean/mathlib `4.34.0-rc2`、こちらは `4.32.2` で、原稿の分散1の入力は既存の `gaussianReal_stein` と `pi_gaussian_stein_coord` で満たせたため移植しなかった。移植後の保守性を比較した記録はなく、旧スカラー部分積分 API は別に残した。

Hermite の直交性・階乗ノルムと有限射影を証明した後、指数モーメントによる有限測度の一意性と特性関数の一意性から有限積ガウスの多項式稠密性を証明した。`hermiteOrthonormal_dense` と2つの無条件 `HasSum` が、任意の実 `L²` クラスについて展開と次数和の収束を与える。研究者は原稿 `eq: chaos` を `L²` 等式として読むことを確認した。条件付き `HasSum` だけを完全性と扱っていない。

個別 Lean 検査、`lake -f lakefile.toml --old build Model SuperConcentration CLT`、同時 import と主要公理確認は成功した。対象は通常公理のみで未検証の仮定なし。古い親設定での `lake build SYK` は休止中 Blueprint の import と整合せず失敗したため、当時は関連ライブラリを指定して検査した。既存警告と当時未完成の最終 CLT は区別して報告した。

<a id="clt-w06"></a>
<a id="merge-f01-2026-09-27"></a>

## 有限模型の基盤と統合障害（2026-09-24–27）

9月24日の検査では有限模型の恒等式・条件付きアニール補題・凸導関数補題・共有集中結果は通常公理のみ、`partition_moments` と最終 CLT、独立 Annealed_FE の主結果は `sorryAx` に依存していた。旧 `AnnealedInput` は解析性・共通半径・逆温度ゼロの近傍での展開も仮定しており、公理依存だけでその構築を証明済みとはしなかった。

W06 で反交換関係・巡回トレースによるトレース零、固有値への Jensen による `Z≥1`、指数支配によるモーメントと対数の可積分性、`Y` の正値性・期待値1・二乗可積分性、正しい対数中心化、逆温度ゼロでの恒等式、標準表現との規格化を完成した。有限模型の公開30定理は通常公理のみで `AnnealedInput` と最終 CLT を使わない。

初回 Main の `incompatible header` は依存再構築で解消した。関連 `lake build CLT` は旧 `Tool.lean` の `unknown module prefix 'RequestProject'` で失敗した。本文・Blueprint・Lean の参照を調べ、未使用だった Tool を依頼に従って削除した後、`lake build CLT` と Main 個別検査が成功し W06 を完了した。後に Tool を現行 mathlib の特異値・Schatten・トレース指数微分の補助として再実装し、`lake -f SYK/workspace/lakefile.toml env lean SYK/CLT/Lemmas/Tool.lean` と `build CLT` が成功した。有限模型の完成とは分けて記録した。

統合版 `84bfde3` は個別ビルドに成功しても、Main と `CliffordSignParity` の同時 import が `SYK.partitionFunction.eq_1` の衝突で失敗した。9月27日に重複定義を除き共有の通常トレースの分配関数を直接使う形に修正し、個別検査・`lake build CLT`・同時 import が成功した。規格化除算、スケール、実部、積測度からユークリッド測度への移送は別に F02 で照合した。

<a id="main-statements-2026-09-18"></a>

## CLT 定理文の初期導入（2026-09-18）

一般 `MajoranaSystem` の設定と主定理を、ユーザーが明示的に `sorry` を許可した依頼に従って追加した。実表現次元による規格化、`Setting q`、サイズ別の測度、分布収束、共通半径と分散を明示した。`lake env lean SYK/CLT/Main.lean` と `lake build CLT` は成功したが、当時の主定理は `sorryAx` に依存していた。この記録は新たな未検証仮定の導入許可ではなく、後の証明完成と区別する。

<a id="model-w01"></a>

## 共有模型・解析の再設計と検証（2026-09-07–08）

逆温度を `Params` から除き、解析は `z : ℂ`、物理的結果は `β : ℝ≥0` の明示引数とした。通常トレースの分配関数と必要な規格化トレースを分け、密度行列・ギブス解析を Model へ集約した。反交換族の評価は集中側に置き循環を避けた。`lake build Model SuperConcentration` と主要公理確認が成功し、通常公理のみだった。

W01 は `Z_H(z)=Tr(exp(-zH))` の複素微分、全点の解析性、非零点での対数微分を仕上げた。自己共役性や対数の枝の存在をこの一般結果へ要求しない。`lake env lean SYK/Model/FiniteDimensionalGibbs.lean`、関連ビルド、4主要定理の公理確認と Model 章の個別検査が成功した。既存の未使用仮定・書式・docstring 警告が残った。

移行対象外の `Annealed_FE/main_result.lean` が旧 `Params.β`・`Params.β_nonneg` を参照したため、当初の全体 `lake build` と `lake exe vbp build` は失敗し、`vbp check` は manifest 不在だった。9月8日に独立2ライブラリを一時除外した後、関連・既定ビルドと生成・参照検査が成功した。既定対象から除いても他ファイルの import 経由の検査を除けるとは限らず、9月24日の Main は独立 Annealed_FE を依存に持っていた。

<a id="gaussian-foundation"></a>

## 独立したガウス基盤と Windows の生成対処（2026-09-11–12）

ガウス基盤を任意有限型上の3ファイル、名前空間 `SYK.GaussianConcentration` に分離した。MGF は `L≥0` のパラメータ `Real.toNNReal (L²)`、正の `L` の裾は `exp(-t²/(2L²))` とその2倍、`L=0` は定数性から別に処理する。個別検査・`olean` 生成・主要公理確認が成功し、通常公理のみだった。

共同研究環境の親 `lakefile.lean` が配布用 TOML より優先し、旧 mathlib と未登録 Verso のため初回 `lake build SYK` は失敗した。他研究の設定を保ち、承認後に Lean/mathlib を4.32.2、Verso を4.32.0へ整合させ、`lake build Model SuperConcentration` と `lake build SYK` が成功した。

Verso 4.32.0 は Windows で同梱検索資産の相対接頭辞を残し、出力先外へのパスを生成した。このため旧 `BlueprintMain.lean` に Windows 限定の準備・コピーを追加し、直接生成と `lake exe vbp check --site SYK/_out/site` が成功した。この対処は現行 `Blueprint/Build.lean` に保持されている。汎用基盤の既存 linter・非推奨警告は残り、局所的な `aesop`・`grind` の整理は現在も保守課題である。

<a id="super-w03"></a>
<a id="super-w04"></a>
<a id="super-w05"></a>

## 標準ハミルトニアン・表現・集中結果（2026-09-18）

W03 は `σ_N²=(q-1)!/N^(q-1)` の標準ハミルトニアンを Model に共有し、集中側の一般スケール `𝒥` の引数・重複定義を除いた。係数の分散と標準ガウス座標で測るリプシッツ性を区別した。Model と集中側の個別検査・`lake build Model SuperConcentration`・主要公理確認が成功した。既定ビルドと当時の Blueprint 生成・参照検査も成功した。

W04 は Jordan–Wigner 表現、次元 `2^(N/2)`、生成子の関係式、同じ偶数次数の相互作用の規格化トレース直交性を証明した。Pauli Y の符号・テンソル順・0始まりとノートの1始まりの対応を照合した。固定次数の直交性には既約性の追加仮定を要さず、異なる次数の族まで主張しない。語・二乗・交換の補題を Model に共有し、個別検査・関連ビルド・主要公理確認が成功した。

W05 は密度行列・有限サイズ二乗和を `DensityMatrix` と `MajoranaBound` に分け、公開 MGF と上下・両側裾、逆温度ゼロの中心化と裾を完成した。有限二乗和 `choose(N,q-1)/q`、標準座標のリプシッツ定数 `β/√q`、MGF パラメータ `β²/q` を保持し、裾の分母を持つ式は `β≠0`・`t>0` に限定した。初回 Main の古い GaussianDisorder 成果物による識別子エラーは共有模型の再構築で解消した。

3変更ファイルと集中章の個別 Lean 検査、`lake build Model SuperConcentration` と `lake build Model SuperConcentration CLT` が成功し、主要15定理は通常公理のみだった。親の既定対象は別研究の `RSATMain` だったため対象を明示して検査した。新規数学警告はなく、汎用基盤の既存警告は残った。

<a id="super-legacy"></a>

旧設計資料の `N^(q/2)` スケール、定数の存在だけを述べる評価、上側裾に `sorry` が残るとの記述は、上記の検証済み結果と一致しない。資料は後の配置整理で削除し、現行 API の根拠にはしていない。

<a id="workspace-migration"></a>

## 生成入口と共有ワークスペース（2026-09-11）

生成入口を旧 `BlueprintMain.lean` に置き、数学の集約 import を廃した。`lake build`、`lake env lean SYK/BlueprintMain.lean`、`lake lean SYK/BlueprintMain.lean -- --run SYK/BlueprintMain.lean --output SYK/_out/site`、`lake exe vbp check --site SYK/_out/site` が成功した。直接生成を採用した理由は当時の `vbp build` がルート直下の入口しか探索しないためである。GitHub CI、任意 PDF、サーバー起動はこの検査に含めなかった。

<a id="chapters-records"></a>

## Verso 休止中の検証範囲（2026-09-18–2026-10-06）

この期間は共有の休止方針により、原則として章・生成入口の Lean 検査、HTML/PDF 生成、`vbp check` を実施しなかった。主張・宣言・依存はソース上で照合し、必要な宣言には Verso を import しない `#check` を用いた。9月18日の章の個別検査成功など、記録された例外はその課題の範囲の検査である。休止中の照合を生成・参照検査の成功と扱っていない。休止中の章更新を含む復帰検証は [10月7日の記録](#verso-restore-2026-10-07) に集約した。

<a id="w-completion-notes"></a>

W01–W06、R01–R05、F01–F08、Z01 の完了はそれぞれ上記の範囲についての記録である。原稿全体の全表示の形式化、外部定理の Lean 証明、`AnnealedInput` の構築を意味しない。現行の対応と境界は [CLT の構造文書](SYK/CLT/ARCHITECTURE.md#現行原稿の主張) を参照する。
