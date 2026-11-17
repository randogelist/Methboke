# Material

`STATUS = EXTERNAL_LEAN_PASS_AT_6440270`. `NO_LOCAL_LEAN` applies to preparation.
The universal analytic admission theorem is outside these endpoint containers.

[Run 44052579373](https://github.com/randogelist/Methboke/actions/runs/44052579373)
passed at `6440270ffe9b05b2956cd34c59c65f2fe341e8b8`: all 283 modules compiled,
14 fresh endpoint audit files covered 41 declaration entries, and the standalone
QFB cutout passed freshly. Exact types and approved standard axioms were checked.
The passed aggregate container and 14 endpoint tags were published, with both
Actions caches saved and the compatible main pointer updated. See the
[source-specific acceptance record](../audits/material-6440270/summary.json).

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

The accepted baseline used the official Mathlib cache and compiled all 283 own
modules from source: dependency/project MISS, native-host execution, 0/283 reuse.
Its job took 37m51s; driver 1479.602s, including 1293.421s own compilation and
39.296s fresh audits; container publication took 534s. The 0.252s no-op receipt
recheck did not execute a second Lean pass. Warm run `44059698760` subsequently
restored the registry snapshot in 264s and completed its verification step in
157s, but publication failed when a 7.67 GB Docker context exhausted disk.
Its matching audit artifact is unavailable; these step timings do not establish
a module-reuse count or a new accepted snapshot.

The prepared warm publication repair inherits the verified dependency directory
from the exact passed image and copies current sources, own outputs and fresh
evidence. It checks disk headroom and preserves verification artifacts before
publication. The cold seed recipe and prior passed image remain intact. External
validation of this repair and a complete warm publication remain pending.

GitHub Actions caches from Methlib are not directly shared across repositories.
Missing Mathlib objects do not authorize a Mathlib source rebuild. Every
acceptance and performance result must identify its exact external receipt.

## Proof scope

Allowed theorem axioms: `propext`, `Classical.choice`, `Quot.sound`. Missing audits, unknown axioms and `sorryAx` fail publication. Source-level or static validation is not a compiler pass.

These containers preserve original theorem premises. They do not prove the new finite-cylinder comparison adapter, the new finite-cap root, or universal analytic germ continuation. Linux CI evidence remains explicitly Linux evidence; native Windows evidence remains separate.
