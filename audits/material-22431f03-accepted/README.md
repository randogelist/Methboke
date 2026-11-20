# Accepted conditional Ehrenfest root

Tested commit: `22431f032c868b8de1526767d7d32a2639f6a9ee`.
External run: https://github.com/randogelist/Methboke/actions/runs/44641040255

The complete 120-member original evidence archive is `evidence.zip`:
212745 bytes; SHA256 `ba080a4d4348de6e2dfe78facf777bb3b74d3aa3f10bd4757163b39f13c35532`.
It includes all 71 fresh package audit logs, the fresh QFB cutout audit,
compiler identity, module logs, source/dependency checks and the full report.
The seven newly accepted package logs and full report are also directly readable here.
The final accepted-job log records `PRIMARY_ACCEPTED: true` and publication success.
The full primary job log is retained losslessly in `fast-job.log.gz`, with hashes
and its exact external job identity in `fast-job-log-manifest.json`.

Accepted scope: 411 modules, 392 reused and 19 fresh; 448 named declarations
plus QFB, with only `propext`, `Classical.choice`, and `Quot.sound`.
This accepts E09.bound and conditional E10. It does not construct a stopped-bound
witness or complete the full Hilbert-operator branch or full E09 H2 convergence.

Independent review: 1488 evidence consistency checks and 534 source/hash checks.
`expected-manifests.json` records all 71 package inventories fetched at the tested SHA.
`pinned-source-review-inputs.json` retains all 71 owned source files and the 14
new wrapper/audit sources fetched at that SHA, with their Git blob identities.
`source-review.json` retains their checked SHA256 identities.

Optional static reproduction uses only Python text/JSON/hash operations:

```sh
python3 -m zipfile -e evidence.zip evidence
python3 review_evidence.py
python3 review_sources.py
```

`review_evidence.py` writes a fresh base evidence-review report; the committed
`independent-review.json` additionally records the separate source review,
observed GitHub final-gate status, and the 183 external Python controls.
No reproduction command invokes Lean, Lake, or a local kernel audit.
