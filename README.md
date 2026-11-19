# Methboke

The current main goal is **Weak_Fourierman_B** for unforced periodic
Navier–Stokes: its full finite squared Fourier budget implies global smooth
continuation of the same maximal trajectory. The budget remains a hypothesis.
Accepted finite-cap R0 and the original QFB endpoints are reusable foundations.
The working branch is **`main`**.

## Current state

**Weak_Fourierman_B is implemented and externally verified.**
[Run 44566880192](https://github.com/randogelist/Methboke/actions/runs/44566880192) at `fdb515d8bde35ec8021bbc26f360aca8dfa2855c` passed all **365 modules**, all **55 fresh endpoint packages**,
**265 declaration audits plus the QFB cutout**, and **183 controls**.
All audited theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
321 accepted modules were reused and 44 additions compiled. Publication and
the final acceptance job succeeded. No local Lean execution occurred.

The [exact root](Material/MethbokeAddon/WeakFouriermanB/WeakFouriermanB.lean)
proves that the full finite squared Fourier budget up to the smaller of the
maximal lifetime and QFB cutoff gives infinite lifetime and a global smooth
pair preserving the original velocity and normalized pressure.
Actual maximal existence for every smooth datum is proved separately.
**The finite budget remains a hypothesis.** Universal budget finiteness and
universal analytic germ extension R1 remain outside this result.

All ten [contextual obligations](PREPRINT_FORMALISATION/WeakFouriermanB/obligations.json)
are accepted. Their [matching evidence](audits/material-fdb515d8/summary.json) retains the 22 new audit logs;
[the A-tier register](Weak_Fourierman_B_A_TIER.txt) and
[cumulative mathematical chain](Weak_Fourierman_B_B_TIER.txt) give exact scope.
The earlier 126-anchor source index remains a historical foundation.

The 269 pinned vendor modules, compiler, dependency lock and CI/cache drivers
are unchanged. R0 and original QFB acceptance remain valid. The two failed
implementation attempts are retained at
[4bd466f1](audits/material-4bd466f1-failed/summary.json) and
[8318b7a6](audits/material-8318b7a6-failed/summary.json).

The [ten-step publication-to-WFB derivation](WFB_TEN_STEP_PUBLICATION_DERIVATION_B_TIER.txt) maps the
[small-H1/2 preprint](https://zenodo.org/records/24185514) to the accepted root.
It separates the smallness-based budget certificate from the general finite-budget
continuation theorem and identifies the additional QFB input.

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
| Finite analytic cylinder gives strong initial trace and finite Serrin norm | A-tier at `93ca8a5`; actual admitted cylinder retained |
| `D_Q(nu) subset R_nu` | A-tier at `93ca8a5`; literal two-sided NSE cap and explicit zero branch |
| Arbitrary-amplitude finite Fourier Beltrami data belong to `D_Q(nu)` | Explicit B-tier solution; no QFB premise |
| `FB_nu <-> (D_germ(nu) subset D_Q(nu))` | B-tier reduction under the recorded foundation interfaces |
| `D_germ(nu) subset D_Q(nu)` universally | Open continuation obligation |
| Classical and two-sided analytic finite-cap roots | A-tier at `93ca8a5`; velocity and normalized pressure preserved on `[0,T)` |

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
baseline. Later accepted cached runs, including `93ca8a5`, record their own
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
proof of universal analytic extension. The accepted R0 inclusion retains an
actual cap premise; universal germ-to-cap extension R1 remains open.


## Current mathematical boundary

The exact WFB finite-budget implication and all ten contextual obligations are
accepted. Its physical H1 local construction uses cutoff-uniform bounds and an
actual Galerkin limit. Its continuation theorem consumes the actual physical
dissipation-square integral and constructs a longer front preserving velocity
and normalized pressure. Strict cutoff overlap includes the equality case;
the accepted R0 theorem then supplies the same-path global pair.

No universal budget bound, arbitrary-data global regularity or universal
analytic germ-to-cap extension is asserted. The actual R0 cap condition remains
explicit in its own theorem and is supplied by the WFB continuation chain.

### Historical R0 verification attempts

[Run 44543421609](https://github.com/randogelist/Methboke/actions/runs/44543421609)
at `0ddd2d67` reused 303 accepted modules but stopped before audits at two
rewrite matches in gluing and pressure uniqueness. Both corrections preserved
every statement. The later scope expanded from 317/31/154 to 321 modules,
33 packages and 161 declarations plus the cutout by adding the literal
two-sided analytic cap and exact data-class adapter.

[Run 44545010863](https://github.com/randogelist/Methboke/actions/runs/44545010863)
at `c6e039da` compiled the earlier corrections but stopped in initial-trace
filter notation and composition normalization. These expressions were repaired
without changing statements or the 321/33/161 scope.

[Run 44547124107](https://github.com/randogelist/Methboke/actions/runs/44547124107)
at `d2c0259` compiled all 321 modules and passed 19 audit packages, including
the literal R0 root, but stopped at an unused namespace in the pressure audit.
The one-line audit setup repair preserved every proof and signature assertion.
These failed attempts did not promote the root or replace accepted caches;
recovery was skipped. The complete compiler/type/axiom gate and publication
subsequently passed in run `44549257770` at `93ca8a5`.
