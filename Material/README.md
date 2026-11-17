# Material

`STATUS = A_TIER_CANDIDATE` until matching external compiler and theorem-level axiom evidence is emitted. `NO_LOCAL_LEAN` applies to preparation. The universal analytic admission theorem is outside these endpoint containers.

[Run 44046225468](https://github.com/randogelist/Methboke/actions/runs/44046225468)
compiled all 283 local modules at `670de211`, then failed in the audit phase on
unsupported option `pp.width`. The remaining audits and single-file cutout
were not completed. No passed cache/container was published. Audit correction
and matching external acceptance remain pending.

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

The configured external Linux workflow invokes:

```sh
bash Material/ci/verify-external.sh
```

Local work is limited to reading, file preparation and nonexecuting static
inspection. Lean, Lake wrappers and kernel audits must run only in the
authorized external environments. Once a CI runner starts, agent work stops
until the user's **go on** resumes result inspection.

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

The first accepted baseline may require the exact official Mathlib cache and
compilation of this repository's own selected source closure. GitHub Actions
caches from Methlib are not directly shared across repositories. Missing
Mathlib objects do not authorize a Mathlib source rebuild. No successful
Methboke baseline or performance result is assumed before an external receipt.

## Proof scope

Allowed theorem axioms: `propext`, `Classical.choice`, `Quot.sound`. Missing audits, unknown axioms and `sorryAx` fail publication. Source-level or static validation is not a compiler pass.

These containers preserve original theorem premises. They do not prove the new finite-cylinder comparison adapter, the new finite-cap root, or universal analytic germ continuation. Linux CI evidence remains explicitly Linux evidence; native Windows evidence remains separate.
