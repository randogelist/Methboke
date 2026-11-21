# Matching external acceptance: d403c235

External source: `d403c235a1cf6db5d9276f7cd987a4cc990a2fdf` on `AC-Integration`.
Run: [44837033211](https://github.com/randogelist/Methboke/actions/runs/44837033211).

This archive records acceptance already produced by external cached Linux Lean 4.33.0. The local review only reads existing logs, JSON, pinned Git objects and hashes. It does not run Lean, Lake, a kernel audit or any project compiler.

## Verified evidence

- 512 passing module receipts: 496 reused and 16 newly compiled externally.
- 99 fresh package audits, with 1,294 unique named type/axiom reports and a separate passing QFB cutout.
- Every named report is matched to its pinned manifest and ordered raw-log blocks; only `propext`, `Classical.choice` and `Quot.sound` occur.
- Original artifact and routing digests, all audit-log digests, exact tested source, 39 closure-source hashes, completed workflow/jobs, publication steps and terminal acceptance are checked.
- The six additional packages contain 307 names: 252 theorem declarations and 55 definitions/instances.

## Newly accepted scopes

| Package | Names | Theorems | Definitions / instances |
|---|---:|---:|---:|
| QFAStoppedBudget | 63 | 57 | 6 |
| QFAPhysicalStoppedGauge | 42 | 34 | 8 |
| QFAPhysicalH2 | 65 | 45 | 20 |
| QFARealLeray | 72 | 62 | 10 |
| QFARealEvenMultipliers | 24 | 19 | 5 |
| QFAHeatSemigroup | 41 | 35 | 6 |

Exact full types and axiom lists are in `new-declaration-evidence.json.gz`; source identities and package scopes are in `summary.json` and `independent-review.json`. The six package logs are retained as `<Package>.log.gz`, preserving their exact original decompressed bytes and SHA256 digests. The reviewer compares each decompressed log byte-for-byte with the original archive. `acceptance-job.log` and `QFB-cutout.log` remain plain text. `evidence.zip` preserves the entire original 99-package artifact unchanged.

## Scope boundary

The stopped-budget and gauge results cover every pathwise P08 clause in `R3_NSE/A-Regularity-class/A_TIER_STEPLIST.md`. Together with the earlier accepted P01–P07 physical layer, they complete **M1 for supplied physical H1 paths**. The clause-by-clause source and audited-declaration mapping is retained in `semantic-review.json`.

H2, Leray, even multipliers and heat-semigroup results are actual analytical constructions, but this batch does not construct nonlinear NSE evolution, prove full physical QFA/WFA, admit the sharp Sobolev constant, or prove universal budget finiteness. G05 is preserved; no additional G01–G06 PDE gap target is closed. M2 and M3 remain open. The pending language in source-era documentation is superseded only for these exact scopes by this matching evidence.

## Reproduce the nonexecuting review

From the repository root:

```bash
python3 audits/material-d403c235-nse-a-accepted/review_evidence.py . audits/material-d403c235-nse-a-accepted d403c235a1cf6db5d9276f7cd987a4cc990a2fdf 44837033211 7c39509200367c8a47ca5d9a9e9cb052a2adab37bb985d0d47362d322e568307
```

The exact source and policy-baseline Git objects must be available. The review also checks that the six accepted source/audit files have not been changed in the working tree. The test count is a count of static consistency checks, not a replacement for the archived external compiler evidence.
