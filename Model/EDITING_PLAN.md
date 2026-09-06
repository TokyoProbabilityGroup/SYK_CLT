# 共有 SYK 模型の編集計画

## 目的

現在の API との互換性は要求せず、規格化トレース、解析に用いる複素逆温度、物理的な非負の実逆温度、およびマヨラナ系の抽象的な定義と具体的な表現を明確に分離する。

## 段階0：現状と文書の確認

各項目は移行作業の計画であり、チェックの付いていない項目を実装済みとみなさない。現行と目標の型・規格化・ビルド対象の差は `ARCHITECTURE.md` の対応表を参照する。以下のコマンドで使う新名称は、対象の改名と Lake 設定の更新後に有効になる。

- [x] 現在公開されている識別子と、その利用箇所を列挙する。
  - 2026-09-07 時点の `Definitions.lean` の公開宣言は、模型パラメータ
    `Params`（`inverseTemperature` とその型変換に関する補題を含む）、添字の
    `InteractionIndex`・`orderedIndices`・`length_orderedIndices`、抽象代数の
    `MajoranaSystem`（`psiProduct`、`anticommute`、二つの `star_psiProduct`
    補題）、`phase`、`hamiltonian`・`hamiltonian_self_adjoint`、および行列熱力学の
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
    後続項目で、抽象トレース代数も選択肢としている。この設計は、標準の
    `partitionFunction` を規格化トレースかつ複素変数にする移行後の目標とは
    一致しない。
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

## 段階1：モジュールとパラメータ

- [x] `SYK_model/model.lean` を `Model/Definitions.lean` へ移す。
- [x] `lakefile.toml` のビルド対象 `SYK_model` を `Model` へ改名し、理由とすべての利用箇所への
  影響を説明してから変更する。
- [ ] 逆温度を模型のパラメータから削除する。
- [ ] 相互作用の添字、標準的な順序、位相因子、および抽象的なマヨラナ系の API を整理する。
- [ ] 互換性のための別名は作らない。

## 段階2：抽象代数と標準表現

- [ ] 位相因子を含む相互作用演算子と、標準的な規格化によるハミルトニアンを共有定義にする。
- [ ] 偶数 `N` に対する Jordan–Wigner 変換による標準的な行列表現を構成する。
- [ ] 行列の次元、正準反交換関係、自己共役性、および規格化トレースから定まる内積に関する直交性を証明する。

## 段階3：複素行列の解析

- [ ] 非規格化トレースと規格化トレースを定義し、後者を標準にする。
- [ ] 指数関数を取る前の行列に対し、行列指数関数の規格化トレースを定義する。
- [ ] `partitionFunction (z : ℂ) H = tr(exp(-zH))` をその特殊な場合として定義する。
- [ ] `partitionFunction` を定義に沿って展開すると `rawPartitionFunction / card d` になるように
  定義配置にする。
- [ ] `Z(0)=1`、整関数性、および複素微分の公式を証明する。
- [ ] `Z z ≠ 0` の仮定の下で対数微分の公式を証明する。

## 段階4：物理的なギブス状態

- [ ] `β : ℝ≥0` に限定した分配関数の正値性を証明する。
- [ ] 熱平衡状態の密度行列、ギブス期待値、および分配関数の実対数を定義して検証する。
- [ ] 非規格化・規格化トレースによるギブス期待値の対応と、中心化した `log Z` の対応を証明する。

## 段階5：ガウス型相互作用と利用側の移行

- [ ] `CouplingSpace`、標準的な規格化係数 `σ_N`、標準ガウス測度を共有模型に置く。
- [ ] 汎用的なガウス集中不等式の定義を共有模型に混入させない。
- [ ] `SuperConcentration` を新 API へ移行する。
- [ ] CLT との接続部分を `SYK/CLT/ARCHITECTURE.md` と照合する。
- [ ] `Annealed_FE` は編集せず、既知の破損を正確に記録する。

## 後で扱う課題：零点のない領域

- [ ] 固定したハミルトニアンに対する実軸近傍など、最初に証明する具体的な零点のない領域を選定する。
- [ ] 高温領域に対応する円板または帯状領域で一様な評価が必要か、CLT の要件と照合する。
- [ ] 零点がないことを示す定理から、対数を扱う条件付き API に必要な仮定を供給する。
- [ ] 単連結領域上の正則な対数を、必要な場合だけ構成する。

`Z z ≠ 0` を全複素平面で証明することや、複素逆温度におけるギブス演算子の正値性を示すことは目標にしない。

## 検証条件

各 Lean ファイルを個別に検査し、`lake build Model SuperConcentration` を実行する。主要な定理では `#print axioms` を確認する。新しい `sorry`、`admit`、`axiom`、未解決の証明目標は許容しない。ワークスペース全体のビルドに失敗する場合、許容する既知の失敗は未移行の `Annealed_FE` に限り、その内容を報告する。
