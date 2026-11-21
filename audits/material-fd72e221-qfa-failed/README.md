# Matching external source failure: fd72e221

Source `fd72e2218553f6eb89532a4548552d42ba8476f8`, tree `60af2cec39b3e6e03c2fedfa331b8c9315c6b291`, external [run 44845844062](https://github.com/randogelist/Methboke/actions/runs/44845844062).

The cached external Lean 4.33.0 worker passed static admission and reused all 512 prior modules. The new `PhysicalRoot` and repaired `MomentumTranslation` sources compiled. `HeatSmoothing` and the newly unblocked `LHRestart` failed compilation; four dependent modules were blocked. No independent package audits ran, and the acceptance gate failed. Routing classified this as a proof/type failure, so recovery was not attempted.

## Actual compiler diagnostics

- `HeatSmoothing.lean:65`: the cancellation tactic leaves right multiplication, while `hbound` has left multiplication; the remaining goal needs the corresponding commutativity/cancellation normalization.
- `HeatSmoothing.lean:278`: the selected `add_le_add_left` statement has the opposite additive orientation from the displayed target.
- `LHRestart.lean:48`: the selected `add_le_add_right` statement yields `s + r <= s + t`, while the target needs `r + s <= t + s`.
- `LHRestart.lean:60`: the initial-value `simp` makes no progress.
- `LHRestart.lean:87,102,116,120,141`: unqualified `timeTranslate` resolves to the new `LerayHopf.timeTranslate` theorem instead of the original clock function. Both velocity and gradient occurrences require unambiguous qualification.

Full diagnostics remain in the original ZIP and four retained `.log.gz` module logs. `MomentumTranslation` now has only deprecation warnings; `PhysicalRoot` has only a namespace linter warning. Exact decompressed log bytes and pinned source hashes are recorded in `independent-review.json`. The failed gate log, complete workflow/job/artifact metadata and original routing ZIP are retained as well.

## Scope

Directly recorded receipts are 514 PASS, two FAIL and four BLOCKED_BY_DEPENDENCY, totaling 520. Of the passing receipts, 512 were reused and two were compiled fresh. The registry plans 102 packages and 1,367 names, including 73 new names across the three candidate packages. This failed run accepts none of those new names; no independent package audit ran. The earlier d403c235 acceptance, including P08/M1, remains the accepted baseline.

## Reproduce the nonexecuting inspection

```bash
python3 audits/material-fd72e221-qfa-failed/review_evidence.py . audits/material-fd72e221-qfa-failed
```

The reviewer reads JSON, ZIP/gzip bytes, hashes and pinned Git source objects. It never executes Lean, Lake or a kernel audit.
