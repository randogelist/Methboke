# Methboke

Analytic initial admission for the unforced periodic Navier–Stokes equation,
with the original Quasi-Fefferman-B (QFB) endpoint copied into this repository.
The working branch is **`main`**. The fixed mathematical goal is unchanged.

## Current state

- **Weak_Fourierman_B is now a repository workstream:** the
  [workflow plan](PREPRINT_FORMALISATION/WeakFouriermanB/WORKFLOW_PLAN.md),
  [B-tier derivation](Weak_Fourierman_B_B_TIER.txt), ten-obligation register and
  four exact source modules are registered with 57 new declaration audits.
  The full run covers 18 packages, 98 declarations and the QFB cutout.
  All ten obligations await matching repository A-tier evidence.
- **Chat-only progress signs:** `<->` is issued for a complete verified WFB
  obligation or root during an active review. No scheduled monitoring.

- **Native QFB source is present:** 74 QFB modules and 195 required
  SingularClosure modules, preserved at their pinned source bytes.
- **Native binary reuse passed at `66052f4`:** all 283 project objects were
  reused; all 14 endpoint audits covering 41 declarations and the QFB cutout
  passed freshly with standard axioms only in [the 4m59s run](https://github.com/randogelist/Methboke/actions/runs/44080437531).
  All 139 control tests passed. The verified project archive is 25,391,076 bytes;
  [matching evidence](https://github.com/randogelist/Methboke/actions/runs/44080437531/artifacts/14327621291)
  belongs to that exact source and attempt. Existing GHCR images remain available.
- **Full recovery passed twice at `b1178b8`:** the 32 GiB disk guard, all 147
  controls, 283 fresh module builds, every fresh audit and replacement publication
  passed. [Attempt 2](https://github.com/randogelist/Methboke/actions/runs/44086819243/attempts/2)
  took 35m07s. Its red fast job was an intentional drill trigger, not a recovery crash.
- **Normal CI routing now distinguishes cache failures:** commit-message drill triggers are
  removed. Normal runs try the cached worker; manual `force_rebuild=true` selects
  recovery directly. Only explicit current cache rejection may select automatic recovery.
  Proof, audit, static and publication failures preserve the accepted baseline.
  Docker Hub work is paused. Subsequent read-only job metadata shows fast-job
  success and skipped recovery at [44126844972](https://github.com/randogelist/Methboke/actions/runs/44126844972)
  on `43530b7`; its retained report and all 15 audit-log hashes are now checked in
  [the baseline review](audits/material-43530b7/summary.json).
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
| [Weak_Fourierman_B](PREPRINT_FORMALISATION/WeakFouriermanB/README.md) | Scoped Fourier-budget proof, source candidates, workflow plan and ten-obligation ledger |
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
verified binary archives during the pilot. The manual `registry` backend retains
passed containers in `ghcr.io/randogelist/methboke-material`; prior images remain
available. Cache misses and warm measurements are reported distinctly.

The accepted first baseline was a cold seed: both caches missed, all 283 own
modules were compiled, and official Mathlib objects were restored. The job took
37m51s; its driver took 1479.602s, including 1293.421s compiling own modules and
39.296s for fresh audits. Container publication took 534s. These are cold
baseline measurements, not warm rerun timings.

The disk failure in warm run `44059698760` is retained as infrastructure history:
its verification step succeeded but publication copied a 7.67 GB context and
exhausted disk. It supplied no retained matching audit artifact. The corrected
[run 44066821232](https://github.com/randogelist/Methboke/actions/runs/44066821232) passed completely: restoration 212s,
SDK cleanup 48s, compilation/fresh-audit step 141s, and publication 55s.

The container-native run verified dependency use directly inside the passed
container and export of only current project outputs and evidence. Restoration
fell from 212s to 117s. SDK cleanup took 77s and fresh audits 110.849s; neither
phase was skipped. All exported object hashes were checked before publication.
The 41s overall improvement is a single observation, and the prior run rebuilt
one wrapper whereas this run rebuilt none.

The `MAYBE ;AYBE` comment benchmark passed in 9m08s: 282 objects reused and
only its wrapper rebuilt. Its unchanged manual rerun passed in 8m13s with all
283 objects reused. These are GHCR measurements; the original empty-commit
timing remains unmeasured because its pending run was superseded.

Pushes default to `binary_cache`; manual `backend=registry` retains the GHCR
path. The fast worker requires compatible dependency and project caches with a
prior PASS report, compiles amendments and runs all audits freshly. An explicit current-run rejection of missing or unusable cached objects may
select a separate recovery runner at the same source commit. Proof, type, axiom,
static, publication, cancellation and unknown failures do not select recovery. Recovery restores no project
or dependency Actions caches: it obtains pinned official Mathlib objects and
rebuilds every project module before all fresh audits. Mathlib source compilation
is not allowed; an unavailable official dependency cache remains a blocking error.

After verification, recovery publishes a replacement receipt-checked project
archive and new immutable dependency/project cache generations. Future fast runs
prefer these healed keys. A final verdict requires a fully accepted fast or
recovery result, including successful publication; cancellation does not launch
recovery. Strict `exact_cache_benchmark=true` runs retain their miss-fails behavior.
The manual registry backend does not enter this new recovery path.

Binary artifacts have 90-day retention and distinct `-fast`/`-recovery` names;
Actions caches are the current restoration input. Artifact expiration alone does
not require rebuilding while compatible caches remain. If caches are unavailable,
recovery recreates them and supplies a fresh archive. No binary is committed to Git
and no durable dependency-release backup is claimed. Both binary workers avoid
Docker operations. Full recovery passed twice; subsequent fast reuse of its
replacement caches remains to be measured.

The first native binary round passed in 4m59s; repeat/comment rounds remain pending.
[The first recovery drill](https://github.com/randogelist/Methboke/actions/runs/44085694998)
failed its disk preflight and correctly failed the final acceptance gate. No new
compiled package was published. The repair applies a step-local 32 GiB cold budget
to binary recovery only; fast verification remains at 20 GiB and registry cold
publication at 40 GiB. The 32 GiB recovery passed twice at `b1178b8`, with
147 controls, 283 fresh modules, all fresh audits and replacement publication.
The old commit marker deliberately failed the first worker on every rerun; it
is removed from the revised routing. Manual `force_rebuild=true` now skips the
fast job and selects recovery directly. Combining it with strict benchmarking
or the registry backend fails preflight without recovery. New pushes supersede
older active work; manual reruns remain queued. Rerunning an old workflow uses
its old configuration. After a new CI run starts, independent implementation may continue while that
exact commit is verified. Available results are inspected without requiring a
new **go on**; no scheduled monitor is used.

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


## Current WFB migration boundary

The WFB B-tier chain derives global regularity of the same trajectory from a
finite full squared Fourier budget; it does not prove that budget for every
datum. See [the exact cumulative statement](Weak_Fourierman_B_B_TIER.txt).
The active source layer preserves all four candidate proof files, the 269 vendor
modules and dependency pins. A versioned adapter reconstructs legacy receipt
identities and verifies restored object bytes before reuse; all audits run freshly.
The first activation still needs matching external acceptance.

The next formal obstruction is physical periodic H1 local existence with a
cutoff-independent norm-controlled lifespan. Existing Galerkin existence does
not provide it. A separate seven-declaration smooth-datum admission helper is
[prepared only](PREPRINT_FORMALISATION/WeakFouriermanB/next/REVIEW.md).
The exact WFB and finite-cap roots remain unverified; the fixed goal is unchanged.
