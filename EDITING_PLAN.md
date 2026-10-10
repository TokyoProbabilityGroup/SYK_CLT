# SYK の未完了作業

この文書は未完了課題の状態と着手条件を管理する。規則は [AGENTS.md](AGENTS.md)、現行の数学的仕様は各構造文書、完了した成果と検証は [作業履歴](WORK_HISTORY.md) を参照する。Model と SuperConcentration に持ち越した実装課題はない。

## 残る作業

| 作業ID | 課題 | 状態・着手条件 | 担当・統合 |
| --- | --- | --- | --- |
| `CLT-CONVEX` | 各点収束から関数・導関数の局所一様収束を導く | 保留。再開時に対象と検証範囲を指定する | 未割当 |
| `CLT-EXTERNAL` | 引用元と `AnnealedInput` の構築に必要な外部入力の調査 | 保留。参照原稿・引用元の版を定めて読み取り調査する | 未割当 |
| `CLT-ANNEALED` | 明示した外部入力から `AnnealedInput` を構築する | 保留。上記調査後に外部仮定の採否・正確な型・編集範囲を確定する | 未割当 |
| ガウス基盤の保守 | 書式の警告（長い行・`refine'`・柔軟な `simp`、約450件）を解消する | 独立した保守課題。探索タクティク・非推奨 API・`maxHeartbeats` は整理済み | 未割当 |
| 公開の経路 | LICENSE と `lakefile.toml` のメタデータ、README の利用手順（`require` で使う方法）、リポジトリ名の確定、親の雛形なしでの `SYK`・`SYKBlueprint` 単体のビルドの CI、GitHub Pages での Blueprint 公開 | 保留。ライセンスの種類と公開範囲を共同研究者と決めてから着手する | 未割当 |
| `DOCS-CLEANUP` | 内部文書と話題別 README の整理 | 進行中。小項目と状態は [文書の整理](#文書の整理docs-cleanup) に記す | Kamijima |

数学的仕様と完了条件は [CLT の計画](SYK/CLT/EDITING_PLAN.md) と [ガウス基盤の計画](SYK/Probability/GaussianConcentration/EDITING_PLAN.md) に記す。条件付き CLT と標準模型族への適用は検証済みだが、`hFE : AnnealedInput` の構築と `prop:annealed-free-energy` 自体の証明は未完了である。

公開の経路のうち GitHub Pages は、Verso Blueprint の雛形（`blueprint-pages.yml`）を土台にし、`Blueprint/` の直下で `lake exe cache get` と `lake exe vbp build` を実行して `Blueprint/_out/site/html-multi` を公開する。Pages の URL はリポジトリ名に依存するので、名前を確定してから設定する。

`CLT-CONVEX` と `CLT-EXTERNAL` は独立に調査できる。入力構築は必要な凸収束補題と外部入力の仕様を受け取って進める。並行候補の記載は複数エージェントの起動許可ではない。

## 文書の整理（DOCS-CLEANUP）

公開に向けて、内部文書と話題別の README を整理する。小項目は表の上から1つずつ進め、終えたら同じ差分で状態を「完了」にする。再開するときは、この表と `git log`・`git status` を確認する。未コミットの差分があれば、最初の「未着手」の小項目が途中まで進んでいる。全項目を終えたら、この節と「残る作業」の行を削除し、作業履歴に記録する。

方針は次のとおりである。

- ルートの `README.md` は編集しない。28行目にある日本語の構造文書へのリンクは、修正を提案するだけにする。
- 英語の README から日本語の内部文書へのリンクは外し、必要な事実を英語で書く。Lean ソースと Blueprint の章へのリンクは残してよい。
- `WORK_HISTORY.md` は書き換えず、古くなったリンクだけを直す。

| 小項目 | 内容 | 完了条件 | 状態 |
| --- | --- | --- | --- |
| DOC-0 | この節を追加する | — | 完了 |
| DOC-1 | 本計画の手順を `AGENTS.md` へ移す。「原稿改訂と実装の同期」は新しい節「原稿の改訂と実装の同期」に、「共同作業の引き継ぎ」と「別環境への引き継ぎ」は「作業範囲と分担」の小節に、「Blueprint の更新」の規則は「ビルドと Blueprint」に移す。CLT 課題を再開したときの章の更新は、CLT の計画の「着手と検証」に移す。README の規則を「ルートの `README.md` と原稿本文は人間が管理する。話題別の README と `workspace/README.md` は必要な範囲で編集してよい」に改める | 旧アンカーへのリンクが残らず、リンク検査の不備が0件で、移した規則の効力が元と一致する | 完了 |
| DOC-2 | CLT の構造文書と計画から、履歴（`CLT-APPLY` の完了、互換用の別名を足していないこと、「一本化した」、`Annealed_FE` の削除）とエージェントへの指示（索引の節の冒頭にある `AGENTS.md` の確認範囲）を除く。2つの Mermaid 図を現在の import と宣言に照合する | 現在の仕様だけが残り、図が現行と一致する | 完了 |
| DOC-3 | 構造文書の「補助 Lean ファイルの役割」にだけある情報を、各モジュールの docstring へ英語で移し、節を短い案内に置き換える。CLT の README と計画にある索引へのリンクを直す | 索引の情報が docstring にあり、変更したファイルの個別検査と `lake build SYK` が成功する | 完了 |
| DOC-4 | CLT・SuperConcentration・`workspace/` の README から日本語の文書へのリンクを外し、定理文の所在、残る課題、公理依存を英語で書く | これらの README に日本語の文書へのリンクが残らない。公理依存は `#print axioms` で確かめる | 未着手 |
| DOC-5 | CLT とガウス基盤の `AGENTS.md` を、Model・SuperConcentration と同じ簡潔な形に書き直し、上位と重複する定型文を削る。4つの冒頭の文をそろえる | 規則の効力を保ち、上位との重複が残らない | 未着手 |
| DOC-6 | `SYK/AGENTS.md`、3つの計画、3つの構造文書の日本語を読みやすくする。「・」でつないだ名詞の列は文や箇条書きに開き、長い文は分ける | 数学の内容と規則の効力が変わらない | 未着手 |

小項目ごとに、リンク検査（全 `.md` の相対リンクについて、ファイルと見出しアンカーまたは `<a id>` の存在を確かめる）と差分の照合を行う。
