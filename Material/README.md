# Material

`STATUS = A_TIER_CANDIDATE` until matching external compiler and theorem-level axiom evidence is emitted. `NO_LOCAL_LEAN` applies to preparation. The universal analytic admission theorem is outside these endpoint containers.

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

External Linux CI invokes:

```sh
python3 Material/ci/build.py --report Material/registry/current.json
```

Static source preparation, without invoking Lean:

```sh
python3 Material/ci/build.py --validate-only
python3 -m unittest discover -s Material/ci/tests
```

## Registry and incremental rebuild contract

1. Each push selects the branch's last **passed** GHCR image with matching Linux/AMD64 platform, compiler, dependency lock and cache contract.
2. The container receives the current source checkout; its previous `.lake` compiled artifacts and audit registry remain available. Content-equal source files retain their timestamps.
3. Lake rebuilds changed modules and their transitive dependents. Endpoint audits are reused only when their complete inputs and saved evidence hashes match; changed audit inputs are checked again.
4. A second no-op build records rerun time. Initial compilation, affected compilation, audits and rerun measurements are reported separately.
5. Only a successful compiler/type/axiom result creates immutable aggregate and per-endpoint registry tags. A failed run cannot replace the passed pointer.
6. The mutable branch pointer updates only if the run's commit is still the current branch head. Earlier successful images remain accessible under immutable tags.

Registry package: `ghcr.io/randogelist/methboke-material`. Compiler reports, exact declaration types, axiom lists and transport/registry metadata are uploaded as GitHub Actions artifacts. Image tags and digests are recorded in the resulting registry entry.

The bootstrap has no previous theorem image; it obtains the exact Mathlib compiled cache and builds the extracted local closure. Subsequent runs execute the last compatible passed container. A changed compiler or dependency lock starts a separate compatible cache lineage.

## Proof scope

Allowed theorem axioms: `propext`, `Classical.choice`, `Quot.sound`. Missing audits, unknown axioms and `sorryAx` fail publication. Source-level or static validation is not a compiler pass.

These containers preserve original theorem premises. They do not prove the new finite-cylinder comparison adapter, the new finite-cap root, or universal analytic germ continuation. Linux CI evidence remains explicitly Linux evidence; native Windows evidence remains separate.
