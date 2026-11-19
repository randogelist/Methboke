# Material

`STATUS = FINITE_FRONT_PASS_AT_67f7663; R0_ADMISSION_PENDING`.
The retained baseline has matching evidence at `43530b7`; the first four WFB modules have their own matching pass at `0402aa37`.
See [the acceptance record](../audits/material-0402aa37/summary.json). `NO_LOCAL_LEAN` applies to preparation.
The universal analytic admission theorem is outside these endpoint containers.

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

Each endpoint folder contains the import boundary, exact declaration/audit requests, dependency closure and immutable upstream provenance. `_vendor` contains all 269 actual local Lean source bodies; no private Methlib checkout is required during CI. Shared source bytes prevent duplicate rebuilding across endpoints.

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

The prepared external Linux workflow invokes `container_workspace.py` for a
restored passed image, and `verify-external.sh` for native-host fallback and
exact-cache measurements. The container-native path is pending its matching
external verification; both use the same pinned compilation and fresh audit driver.

Local work is limited to reading, file preparation and nonexecuting static
inspection. Lean, Lake wrappers and kernel audits must run only in the
authorized external environments. Independent implementation may continue
while CI verifies the committed source; inspect results when available.

## Registry and incremental rebuild contract

The working branch is `main`. The first verification runs on the external
Ubuntu 24.04 host with Lean 4.33.0. Subsequent commits execute amendments inside
the exact last passed GHCR container, with restored objects, current source and
a read-only mount of the pinned compiler. Exact-cache benchmarks use the host.

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

The next prepared optimization leaves both dependency and cached own objects
inside the exact passed container, overlays current source, and exports only
fresh evidence and own build outputs. Exported object hashes must match their
receipts. Conditional SDK cleanup reclaims only enough allowlisted space for
the current disk budget. These changes remain pending external verification;
283/283 reuse is an expectation for unchanged source, not an accepted result.

GitHub Actions caches from Methlib are not directly shared across repositories.
Missing Mathlib objects do not authorize a Mathlib source rebuild. Every
acceptance and performance result must identify its exact external receipt.

## Proof scope

Allowed theorem axioms: `propext`, `Classical.choice`, `Quot.sound`. Missing audits, unknown axioms and `sorryAx` fail publication. Source-level or static validation is not a compiler pass.

These containers preserve original theorem premises. They do not prove the new finite-cylinder comparison adapter, the new finite-cap root, or universal analytic germ continuation. Linux CI evidence remains explicitly Linux evidence; native Windows evidence remains separate.

## WFB owned-source activation

Four owned sources are registered separately in `owned-sources.json`; they are
not attributed to the pinned Methlib vendor snapshot. The complete native scope
is 317 modules, 31 audit packages, 154 declaration entries and the QFB cutout.
Principal WFB theorem types are explicitly asserted before their fresh audits.
Native direct compilation needs no Lake target change. Standalone exports add
the required owned libraries and preserve both provenance classes.

The allowlisted legacy receipt adapter preserves unchanged baseline objects
only after recursive source/import/object identity checks. Full fresh audits
remain mandatory. Unknown compile contexts fail without implicit whole-project
rebuild. Automatic recovery requires a typed current-run cache failure.
No new WFB theorem is accepted until matching external evidence is reviewed.

The subsequent prepared packages WFBFiniteFrontTest, WFBFiniteWindowCrossIdentity,
WFBFiniteWindowRelativeEnergy, WFBFiniteWindowSerrinComparison and
WFBLocalFrontIdentification carry the actual finite-front comparison chain.
Their source proofs and exact signature assertions require external acceptance;
no physical local-existence or global-root conclusion is hidden in a field.

Seven R0 packages register actual compact-cylinder estimates, pressure
uniqueness, finite-cap gluing/overlap, initial-front admission, and the classical
and analytic finite-cap roots. Their34 public declarations have explicit type
assertions and fresh axiom audits. Root admission is a real finite solution
premise; universal extension and arbitrary-data regularity remain outside scope.

Next R0 recheck:321 modules/33 packages/161 declaration audits pluscutout.
The two source rewrite failures at0ddd2d67 are corrected without statement or
driver changes. Literal two-sided analytic-cap and D_Q subset R_nu packages
are included. All root acceptance remains pending matching external evidence.

The c6e039da recheck compiled the earlier gluing/pressure corrections but
stopped in initial-trace filter notation and composition normalization. Those
expressions are corrected; statements and321/33/161 scope are unchanged.
[Retained failed-run evidence](https://github.com/randogelist/Methboke/actions/runs/44545010863)
confirms303 baseline objects reused and recovery skipped. Acceptance is pending.

Run44547124107 atd2c0259 compiled all321 modules and passed19 audit packages,
including the literal R0 root. The remaining required gate stopped at an unused
namespace in the pressure audit. Its one-line setup repair preserves every
proof, signature assertion and axiom audit; full acceptance remains pending.
