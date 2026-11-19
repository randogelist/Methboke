# Methboke

Analytic initial admission for the unforced periodic Navier–Stokes equation,
with the original Quasi-Fefferman-B (QFB) endpoint copied into this repository.
The working branch is **`main`**. The fixed mathematical goal is unchanged.

## Current state

- **Latest accepted package:** [run 44540921991](https://github.com/randogelist/Methboke/actions/runs/44540921991)
  at `67f766330918577e714e326be82eebfe29f5f2f7` verified 303 source modules,
  24 endpoint packages and all 120 declaration audits plus the QFB cutout.
  It reused 291 objects and compiled 12 additions. The
  [matching evidence](audits/material-67f7663/summary.json) accepts actual
  smooth-datum admission and finite-front Leray–Hopf identification.
- **WFB-01 and WFB-02 are accepted** at `0402aa37` with
  [matching evidence](audits/material-0402aa37/summary.json). The complete WFB
  root and the remaining eight contextual obligations remain unresolved;
  accepted helpers retain their exact scope.
- **The fixed R0 finite-cap roots have complete candidate source proofs.**
  [Run 44543421609](https://github.com/randogelist/Methboke/actions/runs/44543421609)
  is checking `0ddd2d67`: 317 modules, 31 packages and 154 declaration audits
  plus the cutout. Classical and analytic admission retain an actual finite cap
  strictly beyond the QFB cutoff as a premise. Exact external acceptance is
  pending; universal analytic germ extension R1 remains open.
- **Cached external verification remains mandatory.** Explicit current cache
  rejection may select recovery; proof, audit, static and publication failures
  preserve the accepted baseline. Independent implementation may continue
  while an exact commit is checked. No local Lean or scheduled monitor is used.
- **Chat-only progress signs:** `<->` is reserved for an accepted complete WFB
  contextual obligation or exact root, not a helper pass or CI status alone.

The 269 pinned vendor modules remain unchanged. Main consolidation is complete;
the retired `Clay-Admission-Candidate-01` branch history is preserved. Docker Hub
work remains paused. Earlier infrastructure measurements are retained below
and in [INDEX-WORTHY.txt](INDEX-WORTHY.txt).

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
| Finite analytic cylinder gives strong initial trace and finite Serrin norm | B-tier argument and complete candidate proofs; R0 verification pending |
| `D_Q(nu) subset R_nu` | B-tier; classical/analytic finite-cap proof sources prepared, exact external acceptance pending |
| Arbitrary-amplitude finite Fourier Beltrami data belong to `D_Q(nu)` | Explicit B-tier solution; no QFB premise |
| `FB_nu <-> (D_germ(nu) subset D_Q(nu))` | B-tier reduction under the recorded foundation interfaces |
| `D_germ(nu) subset D_Q(nu)` universally | Open continuation obligation |
| New finite-cap roots in Lean | Complete candidate proof sources; matching external acceptance pending in run 44543421609 |

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

### Retained historical observations

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

### Current verification behavior

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
Docker operations. Full recovery passed twice at the historical `b1178b8`
baseline. Later accepted cached runs, including `67f7663`, record their own
object-reuse counts and fresh audit evidence.

The historical first native binary round passed in 4m59s. Its scope differs
from later GHCR comment benchmarks and current expanded proof packages.
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


## Current mathematical boundary

The [WFB B-tier chain](Weak_Fourierman_B_B_TIER.txt) derives global regularity of
the same trajectory from a finite full squared Fourier budget. It does not prove
that budget for every datum. Its two Fourier-to-Serrin bridges are accepted,
and the second accepted layer supplies smooth-datum admission and genuine
finite-front comparison with the original weak path. The globally smooth
object used in weak testing is a constructed test; it is not an assumed global
NSE solution.

Physical periodic H1 local existence with a norm-controlled lifespan remains
the next WFB obstruction. Existing fixed-cutoff Galerkin existence does not
supply it. The maximal-trajectory, continuation and exact WFB-root obligations
remain separate from the accepted comparison helpers.

The R0 layer now under verification derives initial trace and compact Serrin
bounds from an actual admitted front, identifies the original weak path,
proves velocity and normalized-pressure agreement with its QFB tail, and
constructs a global smooth splice. The classical and analytic root proofs are
present in `Material/MethbokeAddon/WeakFouriermanB/`; matching external
acceptance remains pending. No arbitrary-data cap or universal germ-to-cap
extension is asserted.

### R0 compilation feedback and exact data-class adapter

[Run44543421609](https://github.com/randogelist/Methboke/actions/runs/44543421609)
reused303 accepted modules but stopped at two syntactic rewrite matches in
gluing and pressure uniqueness. Both source corrections preserve every statement.
No root audits or acceptance followed; recovery was correctly skipped.
The next verification also includes the literal two-sided analytic NSE cap
and exact `D_Q(nu) subset R_nu` theorem, with the zero branch handled explicitly.
Prepared scope:321 modules,33 packages,161 declarations pluscutout.
