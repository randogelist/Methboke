# QFA heat time-energy and all-window budget: matching acceptance

**Source:** `000c1bd9baded808b79a04b7f666cacabce64939`, branch `AC-Integration`.
**External run:** [44851575278](https://github.com/randogelist/Methboke/actions/runs/44851575278).
**Result:** all 526 source modules, 105 fresh package audits and 1,402 named
type/axiom reports passed, together with the original standalone QFB cutout,
required publication and final acceptance gate. Of the source modules,
520 were reused from matching verified objects and six compiled fresh.

The new scope is exactly 35 declarations: 32 theorems and three definitions,
covered by 39 independently typed consumers. The source and audit identities
were independently reconstructed in 10,228 nonexecuting text/JSON/hash checks.
All transitive axiom reports contain only propext, Classical.choice and
Quot.sound. Compiler, dependency pins, existing contracts, cutoff and
verification policy are unchanged.

## Accepted scopes

| Package | Exact accepted scope |
|---|---|
| QFAHeatTrajectory | Actual positive-time physical H2 heat path, equality with the heat velocity/H1 trace, positive-time H2 continuity and strong time measurability |
| QFAHeatTimeEnergy | Exact factor-2ν enstrophy dissipation, integrable actual squared Laplacian, finite-window MemLp2 physical H2 and quantitative H2 time bound for arbitrary actual H1 input |
| QFAWeightedBudgetAllWindows | Actual LH product integrability and bound norm(a)^4/(4ν) for every finite real T≥0, including the empty T=0 window |

The weighted-budget scope closes checklist step7. The H2 path is extended by
zero at nonpositive times solely for measurability/integration; arbitrary H1
input is not claimed to have an H2 initial trace. The actual H1 heat path
retains its original trace. These statements do not construct general-data
LH solutions, forced heat or nonlinear local solutions. General QFA/WFA and
the five remaining G-parent gaps remain open.

## Evidence and reproducibility

- `evidence.zip` is the complete original external artifact14686305544,
  SHA256 `7f0daaf4b7654e137a889775e3ef52a31f942642a8d6839c52a7152827a147fa`.
- `routing-evidence.zip` is original artifact14685762002,
  SHA256 `1623d8f239d7594fe098bab6fc3c2fa5c310249c35d109fa4b96fd0d952a33bd`.
- Matching authenticated workflow, job and artifact metadata and the terminal
  acceptance log are retained alongside `independent-review.json`.
- The three new raw package logs are preserved losslessly as gzip. All35
  literal reported types/axioms are preserved in `new-declaration-evidence.json.gz`,
  with the per-name digest index in `new-declaration-index.json`.
- `review_evidence.py` only reads immutable Git objects and external
  ZIP/JSON/text and computes hashes. It never invokes Lean, Lake, a kernel,
  a compiler or a repository verification driver. Its source-name parser
  recognizes both valid `#check name` and `#check @name` spellings while
  requiring exact ordered manifest coverage.

Reproduce the nonexecuting review with:

```text
python3 review_evidence.py REPO EVIDENCE_DIR 000c1bd9baded808b79a04b7f666cacabce64939 44851575278 3c6fa11713d67bbd1d8d27c067cf5a42317fbf17
```

No local Lean execution occurred. This acceptance is based on cached external
Linux verification, with no native-Windows verification claimed.
