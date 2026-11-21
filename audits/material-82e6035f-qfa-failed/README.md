# Matching external source failure: 82e6035f

Source `82e6035f1fe0b1143b1acd0ee8fa60400df9fde3`, tree `d473e0f11d78cf3b013339c24cc87eed17a0b1a1`, external [run 44846461910](https://github.com/randogelist/Methboke/actions/runs/44846461910).

The cached external Lean 4.33.0 worker passed static admission and reused all 512 prior modules. Six new source modules passed: `PhysicalRoot`, `MomentumTranslation`, `HeatSmoothing`, `LHRestart`, `QFAHeatSmoothing.Endpoint` and `QFALHRestart.Endpoint`. The newly unblocked `ZeroDatum` source failed; only `QFAZeroDatum.Endpoint` was dependency-blocked. No independent package audits ran, and the acceptance gate failed. Routing classified this as a proof/type failure, so recovery was not attempted.

## Actual compiler diagnostics

- `ZeroDatum.lean:90–92`: the unapplied `integrable_zero` constant cannot use `.congr`; its domain, codomain and measure arguments must be supplied.
- `ZeroDatum.lean:95`: the same constant is passed as a proof without its required arguments for the positive-time restricted measure.
- `ZeroDatum.lean:116`: the weak-continuity constant-function proof leaves a topological-space metavariable unresolved.
- `ZeroDatum.lean:231`: the simplification leaves the translated clocks in the supplied restart theorem, while the target uses the opposite addition order explicitly.

Full diagnostics remain in the original ZIP and retained `.log.gz` module logs. The exact decompressed log bytes and pinned source hashes are recorded in `independent-review.json`. The failed gate log, complete workflow/job/artifact metadata and original routing ZIP are retained as well.

## Scope

Directly recorded receipts are 518 PASS, one FAIL and one BLOCKED_BY_DEPENDENCY, totaling 520. Of the passing receipts, 512 were reused and six were compiled fresh. The registry plans 102 packages and 1,367 names, including 73 new names across the three candidate packages. This failed run accepts none of those new names; no independent package audit ran. The earlier d403c235 acceptance, including P08/M1, remains the accepted baseline.

## Reproduce the nonexecuting inspection

```bash
python3 audits/material-82e6035f-qfa-failed/review_evidence.py . audits/material-82e6035f-qfa-failed
```

The reviewer reads JSON, ZIP/gzip bytes, hashes and pinned Git source objects. It never executes Lean, Lake or a kernel audit.
