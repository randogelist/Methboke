# Methboke

Analytic initial admission for the unforced periodic Navier–Stokes equation,
with the original Quasi-Fefferman-B (QFB) endpoint copied into this repository.
The working branch is **`main`**. The fixed mathematical goal is unchanged.

## Current state

- **Native QFB source is present:** 74 QFB modules and 195 required
  SingularClosure modules, preserved at their pinned source bytes.
- **Material passed at `6440270`:** all 283 modules compiled; 14 fresh endpoint
  audits covering 41 declaration entries and the QFB cutout passed with standard
  axioms only in [run 44052579373](https://github.com/randogelist/Methboke/actions/runs/44052579373).
  Exact statements, dependency closures and premises are retained.
- **The passed container is published:** immutable aggregate and 14 endpoint
  tags are registered; dependency and project caches were saved. The
  [source-specific evidence](audits/material-6440270/summary.json) records this
  acceptance. Warm restoration and verification steps succeeded, but publication
  exhausted disk; the last fully accepted baseline remains `6440270`.
- **Main consolidation is complete:** the candidate history is preserved and
  `Clay-Admission-Candidate-01` has been retired.
- **The new analytic finite-cap theorem is B-tier only.** Universal extension
  of an arbitrary analytic germ to the QFB cap remains unresolved.

## Fixed scope and useful identities

Let `nu > 0`, `a` be smooth, divergence-free and mean-zero on the unit
three-torus, and the forcing be zero. Set

```text
tau_Q(a,nu) = ||a||_2^4 / (8*pi^2*nu^5)
T_Q(a,nu)   = 2*tau_Q(a,nu).
```

`D_germ(nu)` admits an actual jointly space-time analytic NSE solution through
`t = 0`. `D_Q(nu)` admits one on `(-epsilon,T_Q)`, with zero handled separately.
The cap is open: attachment at `3*tau_Q/2` provides a strict overlap with the
QFB regular tail. The analytic witness must solve NSE; a formal jet is
insufficient.

| Statement | Exact status |
|---|---|
| Finite analytic cylinder gives strong initial trace and finite Serrin norm | B-tier compactness argument |
| `D_Q(nu) subset R_nu` | B-tier, using the stated LH, relative-energy and QFB interfaces |
| Arbitrary-amplitude finite Fourier Beltrami data belong to `D_Q(nu)` | Explicit B-tier solution; no QFB premise |
| `FB_nu <-> (D_germ(nu) subset D_Q(nu))` | B-tier reduction under the recorded foundation interfaces |
| `D_germ(nu) subset D_Q(nu)` universally | Open continuation obligation |
| New finite-cap root in Lean | Not yet formalized or externally certified |

For a Beltrami trigonometric polynomial, `curl a = mu*a`, the exact solution
`U(t) = exp(-nu*mu^2*t)*a` is jointly analytic for every real time. Its pressure
is `-|U|^2/2` plus the spatial mean of `|U|^2/2`. This supplies the
arbitrary-amplitude BAMBUS/ABC family without proving universal admission.

## Repository map

| Path | Purpose |
|---|---|
| [GPT.txt](GPT.txt) | Fixed goal, mathematical chain, Lean dependency chain and current obligations |
| [INDEX-WORTHY.txt](INDEX-WORTHY.txt) | Short register of substantiated results with exact evidence scope |
| [Material/](Material/README.md) | Independently exportable endpoint packages and shared native source closure |
| [LEAN_CUTOUTS/](LEAN_CUTOUTS/README.md) | Single-file interface aggregation and provenance |
| [CLAY_ADMISSION_CANDIDATE_01_B_TIER.txt](CLAY_ADMISSION_CANDIDATE_01_B_TIER.txt) | Cumulative complete B-tier derivation; historical theorem name retained |
| [PREPRINT_FORMALISATION/](PREPRINT_FORMALISATION/README.md) | Preprint statement anchors and formalization status |
| [PAPER_PREPRINT_PDF/](PAPER_PREPRINT_PDF/README.md) | Reserved paper area; no PDF is represented as completed |
| [audits/](audits/) | Mathlib/Methlib source and evidence reviews |
| [SOURCE_STATUS.json](SOURCE_STATUS.json) | Machine-readable source identities and status boundary |

## CI structure

The implementation follows the two selected Methlib observations:

| Reference configuration | Recorded result | Reused design |
|---|---|---|
| [QFB, Ubuntu 24.04 / Lean 4.33.0](https://github.com/randogelist/Methlib/actions/runs/43801307847) | 4m40s; 74/74 project objects reused, fresh audits | Dependency/foundation/project reuse; two-worker dependency scheduling |
| [H12 integration, Ubuntu 24.04 / Lean 4.33.0](https://github.com/randogelist/Methlib/actions/runs/43361151038) | 3m03s; sixteen checkpoints and frontier regressions | Cache-required warm measurement; exact compatibility validation |

These are historical observations for their original scopes, not promised
Methboke runtimes. GitHub Actions caches are repository-scoped; an upstream
cache label alone cannot supply Methboke's first verified baseline.

The [Material workflow](.github/workflows/material.yml) restores compatible
passed objects, builds amendments and affected dependencies, and runs every
required endpoint/type/axiom audit freshly. Only an accepted result can publish
a passed container to `ghcr.io/randogelist/methboke-material`. Immutable records
preserve earlier passes; a compatible latest-pass pointer serves subsequent
commits. Cache misses and warm measurements are reported distinctly.

The accepted first baseline was a cold seed: both caches missed, all 283 own
modules were compiled, and official Mathlib objects were restored. The job took
37m51s; its driver took 1479.602s, including 1293.421s compiling own modules and
39.296s for fresh audits. Container publication took 534s. These are cold
baseline measurements, not warm rerun timings.

Warm [run 44059698760](https://github.com/randogelist/Methboke/actions/runs/44059698760)
restored the passed container in 264s and completed its compilation/fresh-audit
step in 157s. Publication then exhausted disk while copying a 7.67 GB context.
Those are GitHub step observations; its audit artifact is unavailable, so no
module-reuse count or new theorem acceptance is inferred. The later comment
run also reached publication after a successful 162s verification step.

The prepared repair inherits `.lake/packages` from the exact passed image and
copies current project sources, own outputs and fresh evidence into a small
warm snapshot. It adds disk headroom checks and preserves verification evidence
before publication. This repair still needs external validation. The scoped
recovery workflow can cancel the identified stalled publication. The empty
commit timing remains unmeasured because its pending run was superseded.
After a new CI run starts, agent work stops; **go on** resumes result inspection
and any necessary repair.

Lean execution belongs to authorized external CI or native Windows replay.
The compiler pin is `leanprover/lean4:v4.33.0`; Mathlib is
`db584cd6d46c92f209a44c0f1c829460d327499d`. No local Lean execution is permitted.
Linux evidence is not native Windows evidence.

## Proof boundary

The inherited declaration is
`QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED : QuasiFeffermanBStatement`.
It establishes its literal eventual-tail contract, including energy equality
and uniqueness from post-cutoff traces, under the original data/trajectory
semantics. It does not supply regularity before the cutoff.

`QFBAdmissions.OneRestartOverlapAxiom` and its custom
`QFB_ONE_RESTART_OVERLAP` axiom are excluded. A named certificate field is not a
proof of the missing analytic extension. The new root has **no established
unconditional closure**.
