# Dedicated layout-branch verification

[Run 44651224180](https://github.com/randogelist/Methboke/actions/runs/44651224180) accepted checkout `b730e52ca1e4a661a83a09110378db542455097b` on `codex/reorganize-nse-domains`. The source/layout parent is `eb2a759847abdedfd8ee70d3fbb665f128228ee9`.

The [summary](summary.json) records 411 reused modules, 71 fresh package audits, 448 unique named declarations plus QFB, 183 controls, standard axioms, publication and final acceptance. [Independent review](independent-review.json) passed 4,962 checks. No theorem or stopped-bound witness was added.

`evidence.zip` is the unmodified GitHub artifact containing compiler, source, runtime and fresh audit reports. `review-support.zip` contains the static reviewer and its exact comparison inputs, completed job logs and metadata; see its REVIEW.txt for a replay that never invokes Lean or Lake. The root and bound audit logs and final acceptance log are also retained separately. Later documentation-only commits carry this source-specific evidence and are not new compiler runs.
