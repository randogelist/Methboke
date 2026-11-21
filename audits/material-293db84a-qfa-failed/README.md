# Matching external source failure: 293db84a

Source `293db84a8d2768fdc0d8d07ee0cfa7c5a0b8f9a3`, tree `9866c487a269b6323938991640be30d9b01021a1`, external [run 44845214610](https://github.com/randogelist/Methboke/actions/runs/44845214610).

The cached external Lean 4.33.0 worker passed static admission and reused all 512 prior modules. The new `PhysicalRoot` source compiled. `HeatSmoothing` and `MomentumTranslation` failed compilation; five dependent modules were blocked. No independent package audits ran, and the acceptance gate failed. The routing classified this as a proof/type failure, so recovery was not attempted.

## Actual compiler diagnostics

- `HeatSmoothing.lean:64`: `mul_le_mul_left hprod` resolves to an incompatible signature, so `.mp` is invalid.
- `HeatSmoothing.lean:86`: `fun_prop` lacks a registered continuity result for `heatValue` at this use.
- `HeatSmoothing.lean:248`: the `sq_abs` rewrite does not match; a preceding `mul_pow` expanded the other product first.
- `HeatSmoothing.lean:277`: `positivity` does not close the inverse-coefficient nonnegativity goal.
- `MomentumTranslation.lean:128,135,142`: `inner_zero` is an unknown identifier, leaving the corresponding inner-product-with-zero goals unsolved.

Full diagnostics remain in the original ZIP and the three retained `.log.gz` module logs. The exact decompressed log bytes and pinned source hashes are recorded in `independent-review.json`. `acceptance-job.log`, workflow/job/artifact metadata and the original routing ZIP are also retained.

## Scope

The registry plans 520 modules, 102 packages and 1,367 names, including 73 new names across the heat smoothing, full LH restart and zero-datum packages. This failed run accepts none of those new names. A passing source module alone is not an independent type/axiom acceptance. The earlier d403c235 acceptance, including P08/M1, remains the accepted baseline.

## Reproduce the nonexecuting inspection

```bash
python3 audits/material-293db84a-qfa-failed/review_evidence.py . audits/material-293db84a-qfa-failed
```

The reviewer reads JSON, ZIP/gzip bytes, hashes and pinned Git source objects. It never executes Lean, Lake or a kernel audit.
