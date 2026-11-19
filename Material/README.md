# Material

`STATUS = R0_ADMISSION_PASS_AT_93ca8a5; WFB_ROOT_AND_R1_OPEN`.
[Run 44549257770](https://github.com/randogelist/Methboke/actions/runs/44549257770)
at `93ca8a57536512556ec36717ee933ea52db283bf` accepted all 321 modules
(303 reused, 18 freshly compiled), 33 fresh endpoint packages and 161 declaration
audits plus the QFB cutout. All 183 controls passed and all audited declarations
use only approved standard axioms. See the
[matching acceptance record](../audits/material-93ca8a5/summary.json).
The exact R0 inclusion `D_Q_subset_R_nu` and classical/two-sided analytic cap
roots retain actual cap premises. They do not prove universal analytic admission.
`NO_LOCAL_LEAN` applies throughout preparation.

The following baseline observations are historical and source-specific.
[Run 44066821232](https://github.com/randogelist/Methboke/actions/runs/44066821232)
passed at `73c2e98e68b4f2f53a7de4d0be622e5739066fc3`: 282/283 modules were reused,
the comment-modified QFBRoot.Endpoint was rebuilt, and all 14 endpoint audit
files covering 41 declarations plus the standalone QFB cutout passed freshly.
Exact types and approved standard axioms were checked. The passed aggregate
container and 14 endpoint tags were published, and the compatible main pointer
updated. See the [source-specific acceptance record](../audits/material-73c2e98/summary.json).

The unchanged endpoint manifest status fields record the preparation state;
acceptance is determined by the source-specific external receipts. No later
commit inherits a fresh audit pass automatically. Earlier run `44046225468`
failed on `pp.width` after module compilation and published nothing; the
corrected baseline above supersedes that failure for its exact tested source.

## Endpoint packages

| Folder | Exact source scope |
|---|---|
| `MathlibAnalytic` | Convergent analytic germs, restriction, identity, smoothness, local gluing |
| `MathlibFourier` | Torus Fourier Hilbert basis, convergence, Parseval |
| `MathlibODE` | Picard–Lindelöf, ODE uniqueness, Gronwall |
| `QFBCutoff` | Exact cutoff and safe-cutoff arithmetic |
| `QFBLerayHopf` | Actual physical Leray–Hopf existence |
| `QFBTail` | Smooth tail, energy equality, trace uniqueness, safe cutoff |
| `QFBRoot` | Composed QFB root |
| `QFBRestart` | Almost-everywhere restart and good subcritical time |
| `QFBTraceUniqueness` | Post-trace future uniqueness |
| `SmallH12` | Global small critical-data physical endpoints; smallness retained |
| `Galerkin` | Finite Galerkin global existence and uniqueness |
| `RelativeEnergy` | Finite-interval scalar relative-energy argument |
| `SerrinComparison` | Physical comparison; existing global-reference premises retained |
| `PhysicalNSE` | Positive-time smooth physical realization |
| `WFBPhysicalFourier` | Actual Fourier enstrophy and physical dissipation identities (13) |
| `WFBFourierBudget` | Finite Fourier budget to Serrin with explicit energy premises (5) |
| `WFBLocalFront` | Physical finite-front energy and Serrin bridge (29) |
| `WFBHomogeneousBudget` | Mean-zero homogeneous Fourier-to-Serrin bridge (10) |
| `WFBSmoothDatum` | Actual smooth-datum energy admission and Q01 weak existence (7); WFB-08 input only |
| `WFBFiniteFrontTest` | Globally positive-time smooth velocity test agreeing with the finite front (5) |
| `WFBFiniteWindowCrossIdentity` | Actual localized weak/classical cross identity (1) |
| `WFBFiniteWindowRelativeEnergy` | Finite-window smooth energy and relative-energy transport (3) |
| `WFBFiniteWindowSerrinComparison` | Physical finite-window weak/strong comparison (1) |
| `WFBLocalFrontIdentification` | Same-path original Leray–Hopf identification on the finite front (5) |
| `R0CompactCylinderSerrin` | Actual compact-cylinder bounds and finite Serrin norm (4) |
| `R0PressureUniqueness` | Normalized-pressure agreement on open velocity overlap (9) |
| `R0FiniteCapGluing` | Smooth velocity/pressure splice and physical equation (5) |
| `R0FiniteCapOverlap` | Same weak-path velocity and pressure overlap (2) |
| `R0InitialFrontAdmission` | Initial trace, compact Serrin bound and original weak-path identification (9) |
| `R0FiniteCapAdmission` | Classical finite-cap global admission preserving the front (1) |
| `R0AnalyticCapAdmission` | Analytic forward-cap conversion and admission (4) |
| `R0AnalyticTwoSidedCap` | Literal two-sided NSE cap, forward derivative bridge and admission (5) |
| `R0DataAdmission` | Explicit zero/nonzero data classes and exact `D_Q_subset_R_nu` (2) |

Each endpoint folder contains the import boundary, exact declaration/audit requests, dependency closure and source provenance. `_vendor` contains 269 pinned source bodies; `MethbokeAddon` contains 19 separately registered owned proof modules. No private Methlib checkout is required during CI. Shared source bytes prevent duplicate rebuilding across endpoints.

An independently transferable full cutout is produced by:

```sh
python3 Material/ci/export_endpoint.py QFBRoot --output cutouts/QFBRoot --zip cutouts/QFBRoot.zip
```

The exported directory contains every local source dependency, exact dependency lock, compiler version, audit, build driver and native `run.cmd`. Its only external source dependency is the pinned public Mathlib dependency graph.

## Compiler and dependency identity

```text
Lean       = leanprover/lean4:v4.33.0
Mathlib    = db584cd6d46c92f209a44c0f1c829460d327499d
Methlib    = 96033dd69c994bec337a87369a6c27256e724980
```

`lake-manifest.json` retains all nine exact public dependency revisions. Upstream proof source bytes, Git blob hashes and SHA-256 hashes are recorded in `_vendor/source-manifest.json`.

## External compilation

Native Windows:

```text
Material\run.cmd
Material\run.cmd --endpoint QFBRoot
```

The external Linux workflow defaults to the accepted `binary_cache` path:
restore compatible dependency/project receipts, compile affected modules and
run every required audit freshly. Manual `backend=registry` retains the passed
GHCR container path through `container_workspace.py`. Native-host and exact-cache
verification use the same pinned compilation and fresh audit driver. Current
source-specific Linux acceptance is recorded above; native Windows evidence
remains separate.

Local work is limited to reading, file preparation and nonexecuting static
inspection. Lean, Lake wrappers and kernel audits must run only in the
authorized external environments. Independent implementation may continue
while CI verifies the committed source; inspect results when available.

## Registry and incremental rebuild contract

The working branch is `main`. Cached verification runs externally on Linux
with Lean 4.33.0. The default binary worker and optional registry backend both
validate compatible objects against current sources and pinned dependencies.
Only an explicit current-run cache rejection can select bounded recovery;
proof, audit, static, publication and unknown failures preserve the accepted
baseline without selecting a cold rebuild.

1. Restore compatible dependency objects and the most recent eligible passed
   project snapshot. Validate the toolchain, full dependency lock, source and
   audit-policy identities before reuse. A cache label alone is insufficient.
2. Preserve unchanged foundation/project objects. Schedule amended local modules
   and their transitive dependents in dependency order, starting with two module
   workers. Record module workers and Lean threads separately.
3. Run every configured endpoint type check and theorem-level axiom audit
   **freshly on each verification run**. Retained logs establish historical
   evidence only; they cannot substitute for the new run's required audits.
4. Record cache classification and setup, restoration, build, audit and rerun
   measurements separately. The cache-required warm profile stops with a cache
   miss if its exact prerequisites are absent.
5. Publish immutable aggregate/per-endpoint records only after the complete
   required build and fresh audit pass. Failed verification cannot replace the
   previous passed pointer. Pointer updates must preserve commit ancestry.

Registry package: `ghcr.io/randogelist/methboke-material`. The workflow also
uploads compiler, exact declaration type, axiom and runtime evidence as GitHub
Actions artifacts. See [CI controls](ci/README.md) and the
[registry record guide](registry/README.md) for the executable contract.

The first cold baseline at `6440270` compiled all 283 modules and took 37m51s.
The accepted warm baseline at `73c2e98` took **8m07s**, excluding queue time:
282 objects reused, one rebuilt, restoration 212s, SDK cleanup 48s, verification
step 141s and publication 55s. Driver time was 129.974s, including 37.694s own
build work and 63.615s fresh audits. The 0.476s no-op receipt recheck was not a
second Lean verification. The successful warm snapshot context was 73.42 MB;
it inherited the large dependency directory instead of recopying 7.67 GB.

The later container-native optimization was externally accepted: dependency
and cached own objects remained inside the passed container, current sources
were overlaid, and only fresh evidence and project outputs were exported.
Receipt/object hashes were checked. Subsequent unchanged GHCR runs reused all
283 modules in that historical scope. These measurements do not describe the
current expanded package or replace its matching evidence.

GitHub Actions caches from Methlib are not directly shared across repositories.
Missing Mathlib objects do not authorize a Mathlib source rebuild. Every
acceptance and performance result must identify its exact external receipt.

## Proof scope

Allowed theorem axioms: `propext`, `Classical.choice`, `Quot.sound`. Missing audits, unknown axioms and `sorryAx` fail publication. Source-level or static validation is not a compiler pass.

These packages preserve theorem premises. The current evidence accepts actual
finite-cylinder comparison and the R0 finite-cap roots, including the literal
`D_Q_subset_R_nu` inclusion. Classical and two-sided analytic admission preserve
both velocity and normalized pressure on `[0,T)`. No universal analytic-germ
continuation or arbitrary-data cap admission follows. WFB-01/WFB-02 are accepted;
eight contextual WFB obligations and the exact WFB root remain open. Linux CI
evidence remains Linux evidence; native Windows evidence is separate.

## Owned sources and accepted activation

Nineteen owned proof sources are registered separately in `owned-sources.json`;
they are not attributed to the pinned Methlib vendor snapshot. Together with
269 vendor modules and 33 endpoint wrappers they give the accepted native scope
of 321 modules, 33 fresh audit packages, 161 declaration entries and the QFB
cutout. New theorem types are explicitly asserted before their fresh audits.
Native direct compilation required no Lake target change. Standalone exports
include the needed owned libraries and preserve both provenance classes.

The allowlisted legacy receipt adapter preserves unchanged baseline objects
only after recursive source/import/object identity checks. Full fresh audits
remain mandatory. Unknown compile contexts fail without an implicit project
rebuild. Automatic recovery requires a typed current-run cache failure.

The first four WFB modules passed at `0402aa37`; the six-module smooth-datum
and finite-front comparison layer passed at `67f7663`. All were freshly audited
again in the current accepted package. The constructed globally positive-time smooth velocity
test is not assumed to solve NSE globally. These helpers do not supply physical
local H1 existence or complete the WFB root.

Nine R0 packages add 41 declarations: compact-cylinder estimates, pressure
uniqueness, finite-cap overlap/gluing, initial-front admission, classical and
analytic cap roots, the literal two-sided derivative bridge and exact data-class
inclusion. Their current acceptance is `93ca8a5` / run `44549257770`. Explicit
cap admission remains a premise; universal extension R1 stays open.

## Historical R0 verification failures

The initial `0ddd2d67` run had scope 317/31/154 and failed before audits on two
rewrite matches in gluing and pressure uniqueness. Corrections preserved the
statements; two-sided cap/data-class adapters expanded the scope to 321/33/161.
The `c6e039da` recheck compiled those fixes but stopped in initial-trace filter
notation and composition normalization. The `d2c0259` recheck compiled all 321
modules and passed 19 audit packages, but an unused namespace in the pressure
audit prevented aggregate acceptance. Its one-line setup repair preserved every
proof, signature assertion and axiom audit. Recovery was skipped in all three
failed attempts. The complete corrected scope subsequently passed, with
publication, at `93ca8a5`; the earlier failures remain historical evidence.
