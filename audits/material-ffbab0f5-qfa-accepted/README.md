# Matching external QFA acceptance: ffbab0f5

Exact source: `ffbab0f5a1405b86e1bce105f0ed9881cd5380ef` on `AC-Integration`.
Exact tree: `2216c2cc0cb5dd7d458af538789771111a09db67`.
Successful external [run 44847013775](https://github.com/randogelist/Methboke/actions/runs/44847013775).

The cached external Linux Lean 4.33.0 worker completed compilation, every independent package type/axiom audit, the QFB cutout and required publication. The final `Material accepted` gate passed. The local review only reads existing evidence, pinned source objects, JSON and hashes; it does not execute Lean, Lake or a kernel audit.

## Complete verified scope

- **520 passing modules:** 512 reused and eight fresh.
- **102 fresh package audits:** zero reused audits.
- **1,367 unique named type/axiom reports**, plus the separate passing QFB cutout.
- Every named type and axiom block matches its pinned manifest, expected raw-log sentinel order and report; only `propext`, `Classical.choice` and `Quot.sound` occur.
- All audit-log hashes, original artifact digests, exact source/tree, independent consumer coverage, 39 closure-source hashes, successful publication steps and final acceptance are checked.
- **5,045 nonexecuting consistency checks passed.** These checks inspect the archived external verification; they do not replace it.

## Three newly accepted packages

| Package | Names | Theorems | Definitions / structure |
|---|---:|---:|---:|
| QFAHeatSmoothing | 26 | 20 | 6 definitions |
| QFALHRestart | 18 | 17 | 1 definition |
| QFAZeroDatum | 29 | 16 | 12 definitions, 1 structure |
| **Total** | **73** | **53** | **19 definitions, 1 structure** |

`QFAHeatSmoothing` constructs the actual positive-time physical H1-to-H2 heat map, all nine compact-test weak Hessians, the exact Laplacian Fourier action and quantitative H2 control. Its conclusions do not assume an H2 witness or smoothing estimate.

`QFALHRestart` constructs the full translated physical Leray–Hopf class from a supplied original path at a nonnegative energy start. Actual compact-test weak momentum, all spatial/time integrability clauses, weak continuity, weak gradients and every upper endpoint of the energy inequalities are transported. The existing safe-window selection now supplies full shifted PDE membership.

`QFAZeroDatum` proves the complete strict and closed physical QFA conclusion for the **zero datum**, including actual weak-solution nonemptiness, every supplied zero-datum path, smooth velocity and point-normalized pressure, the original-gradient tail energy equality, and full own-trace future velocity uniqueness. The exact all-data target is also defined and audited; it is not proved.

The exact scope is recorded in `semantic-review.json`. **The general nonzero-data QFA root remains open**, as do WFA, sharp Sobolev admission, canonical class construction and universal budget finiteness. Prior G05 and P08/M1 acceptance is preserved. G01, G02, G03, G04, G06, M2 and M3 remain open.

## Retained evidence

`evidence.zip` preserves the complete original artifact unchanged; `routing-evidence.zip` preserves the original publication/routing record. Complete workflow/job/artifact metadata and the final acceptance log are retained. The three new package logs are stored as `.log.gz`, with exact decompressed bytes and SHA256 digests verified against the original archive. `QFB-cutout.log` remains plain text.

`new-declaration-evidence.json.gz` retains all 73 full types and axiom lists. `new-declaration-index.json`, `independent-review.json` and `summary.json` provide the exact identities and counts.

Original evidence artifact SHA256:

```text
7d5f2bbb61c1bfeacd303448ee412c4487bacc21abe9a624cde2fc40205d092a
```

## Reproduce the nonexecuting review

```bash
python3 audits/material-ffbab0f5-qfa-accepted/review_evidence.py . audits/material-ffbab0f5-qfa-accepted ffbab0f5a1405b86e1bce105f0ed9881cd5380ef 44847013775 7d5f2bbb61c1bfeacd303448ee412c4487bacc21abe9a624cde2fc40205d092a
```

The exact tested source and accepted-baseline Git objects must be available. The reviewer also confirms unchanged local source roots and audit consumers for the three new packages. It never invokes a local compiler.
