# How we formalized the SYK CLTs with AI assistance

This note explains how we used AI to help develop the Lean formalization of our central limit theorems for the SYK model. The authors refined the mathematical arguments, checked the statements and proofs, and decided which changes to accept. AI wrote Lean code and helped with proof search, review, and refactoring. The account below draws on our working practice and examples from the repository's commit history.

## Formalizing and checking the statements

We started by asking AI to write the model and the main claims in Lean before completing their proofs. We then compared these definitions and statements with the reference manuscript, which was kept under `CLT/refs/` and is now in [Paper/](Paper/). We checked the Majorana relations, Hamiltonian and trace normalizations, probability law, parameter ranges, quantifiers, centering, scaling, and limiting variance. Lean checks the proposition actually written down; confirming that it matches the intended mathematics remained our responsibility. The early CLT statements appear in [commit `310ed3a`](https://github.com/TokyoProbabilityGroup/SYK_CLT/commit/310ed3a). We [later added](https://github.com/TokyoProbabilityGroup/SYK_CLT/commit/0fd59f6) the current [SYK/Main.lean](SYK/Main.lean), which presents the model, assumptions, and main claims using mathlib and local definitions. Other SYK modules are used only in the proofs.

## Guiding AI with project documents

To keep later AI sessions aligned with the agreed mathematics, we wrote instructions and supporting documents. These reduced the need to explain the context again and made it easier to spot altered statements, added assumptions, or duplicated work. The first instruction files were [added on September 3](https://github.com/TokyoProbabilityGroup/SYK_CLT/commit/ca690f1). On [September 8](https://github.com/TokyoProbabilityGroup/SYK_CLT/commit/509c978), we explicitly separated the shared workflow from local plans. The documents developed along with the project:

| File | What it recorded and why |
| --- | --- |
| [AGENTS.md](https://github.com/TokyoProbabilityGroup/SYK_CLT/blob/844ba0b/AGENTS.md) | Rules for AI work: preserve the agreed mathematical conventions, state external inputs explicitly, stay within the editing scope, and run the required checks. Local versions added rules for particular topics. These helped prevent AI from replacing a difficult proof with an easier claim we had not intended. |
| [ARCHITECTURE.md](https://github.com/TokyoProbabilityGroup/SYK_CLT/blob/844ba0b/SYK/CLT/ARCHITECTURE.md) | The current mathematical structure: definitions, dependencies, links to manuscript labels, and the distinction between proved results and assumed inputs. It helped authors and AI find reusable results and avoid circular dependencies. |
| [EDITING_PLAN.md](https://github.com/TokyoProbabilityGroup/SYK_CLT/blob/c219750/EDITING_PLAN.md) | Tasks with identifiers, prerequisites, editing scope, status, and completion criteria. A shared plan coordinated the work, while local plans supplied details. This divided the formalization into tasks that could be implemented and reviewed separately. |
| [WORK_HISTORY.md](https://github.com/TokyoProbabilityGroup/SYK_CLT/blob/ed9447c/WORK_HISTORY.md) | Key decisions and their reasons, problems and their solutions, and what verification covered. It preserved context across authors and AI sessions, including why earlier approaches were replaced. Git retained the detailed code changes. |

The plan tracked what remained to be done, while the history explained decisions already made. Most internal instruction files were [removed during release preparation](https://github.com/TokyoProbabilityGroup/SYK_CLT/commit/ef8cbbc). The links above point to earlier versions preserved in the commit history, which readers can adapt to their own projects.

## Dividing the work and reviewing each task

We divided the work among the authors, and each author asked AI to carry out assigned tasks from the plan. These included Gaussian foundations, the Majorana representation, chaos projections, remainder estimates, and the final CLT arguments. Prerequisites determined the implementation order. For example, the history records separate completions of [W02](https://github.com/TokyoProbabilityGroup/SYK_CLT/commit/8fa1e4d), [W03](https://github.com/TokyoProbabilityGroup/SYK_CLT/commit/4a27dd8), and [W04](https://github.com/TokyoProbabilityGroup/SYK_CLT/commit/64ab271), followed by further proof tasks. We assigned responsibility for shared files and coordinated integration whenever one task depended on another's results.

For a similar project, a task request can be as simple as:

> Read the relevant AGENTS.md, ARCHITECTURE.md, and your assigned item in EDITING_PLAN.md. Implement the item using the manuscript statements and existing lemmas it references. Preserve the agreed assumptions and conclusions. Check the files you changed and those that depend on them, report any remaining gaps, and update the task status. If you find a mathematical discrepancy, explain it for human review.

After each task, the responsible author reviewed the changes, compared them with the manuscript, and examined Lean's verification output before accepting the work. An added hypothesis or a changed definition can alter what has been proved even when the build succeeds. Whenever the manuscript changed, we rechecked the affected statements and dependencies, since earlier checks covered only the version they had examined.

## Checking proof completeness and assumptions

Once the planned proofs were finished, we checked for unfinished proofs and examined which axioms the main theorems depended on. A `sorry` placeholder allows compilation while leaving a dependency on `sorryAx`, so a successful build does not establish that all proofs are complete. In the current repository, `lake build` checks the full `SYK` library, including `MainAudit.lean`. After building, readers can put the following in a scratch file named `CheckMain.lean` at the repository root and run `lake lean CheckMain.lean`:

```lean
import SYK.Main

#check SYK.CLT.GaussianSYK.syk_partition_and_log_partition_clt
#print axioms SYK.CLT.GaussianSYK.syk_partition_and_log_partition_clt
```

The output lists `propext`, `Classical.choice`, and `Quot.sound`, the standard foundational axioms used here. The precise claim is therefore that the proofs use no `sorryAx` or axioms added by the project. Theorem hypotheses require a separate check because the axiom report does not list them. The CLTs assume `hFE : AnnealedInput q S`; the annealed free-energy assertions packaged in this input are not proved in the formalization. The [verification guide](SYK/README.md#verification) explains these checks and the remaining input.

## Refactoring and final review

We then used AI agents to refactor the library. They separated general probability results from SYK-specific arguments, consolidated repeated lemmas, simplified proofs using mathlib, and removed unused declarations. The [October 6 reorganization](https://github.com/TokyoProbabilityGroup/SYK_CLT/commit/911c243) and [October 7 simplification](https://github.com/TokyoProbabilityGroup/SYK_CLT/commit/7ec7e63) are examples. We compared declarations before and after changes, reviewed any mathematical differences, and repeated the relevant builds and axiom checks.

Finally, we asked AI to review the code again, with independent agent reviews at designated checkpoints, and the authors assessed the findings. The [final maintenance record](https://github.com/TokyoProbabilityGroup/SYK_CLT/commit/ed9447c) documents this review and verification. We also added [MainAudit.lean](SYK/MainAudit.lean), which checks that the public theorem statements depend only on mathlib and definitions in `SYK/Main.lean`; their proofs may use the rest of the library. This keeps the statements accessible for comparison with the manuscript. In another project, both this mathematical comparison and the mechanical proof checks should continue throughout refactoring.
