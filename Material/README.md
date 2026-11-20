# Material

The current goal is **Fefferman D**, through the finite periodic forced-family
route. The first [foundation package](FeffermanFamilyFoundation/README.md) adds
local blowup, disjoint-carrier and native contract helpers, pending matching
external cached verification. The complete D family root remains unproved; see
the [implementation ledger](../T3_NSE/D-Family-Obstruction/IMPLEMENTATION_STATUS.json).

The prior accepted conditional theorem is
`MethbokeAddon.EhrenfestObstruction.EHRENFEST_OBSTRUCTION`:

```text
forall nu > 0, StoppedCommutatorBound nu -> not (NSE_B nu).
```

[Run 44641040255](https://github.com/randogelist/Methboke/actions/runs/44641040255)
at `22431f032c868b8de1526767d7d32a2639f6a9ee` passed **411 modules**
(392 reused, 19 fresh), **71 fresh package audits**, **448 named declaration
type/axiom audits plus QFB**, and **183 external controls**. Publication and
the final acceptance job passed. The complete original artifact and principal
logs are retained in the [acceptance record](../audits/material-22431f03-accepted/summary.json).

All 183 registered Ehrenfest declarations are accepted. The new principal
scopes are **E09.bound**, actual smooth-front eventual canonical Galerkin
enstrophy boundedness, and **E10**, the exact conditional obstruction.
The stopped-bound witness, full Hilbert-space operator realization and full
E09 H2 convergence remain open. The stopped condition is an explicit theorem
argument, not a global custom axiom.

[Weak_Fourierman_B](../T3_NSE/B-Regularity-class/WFB/Weak_Fourierman_B_A_TIER.txt) remains accepted at
`fdb515d8` / run `44566880192`, with its finite Fourier-budget premise.
The R0 finite-cap results remain accepted at `93ca8a5` / run `44549257770`,
with actual cap admission retained. Universal budget finiteness and universal
analytic-germ extension R1 are not supplied by those results.

## Source and package map

The [endpoint registry](endpoints.json) extends the 71 accepted baseline packages
with the new FeffermanFamilyFoundation package. It lists their
exact declaration requests. Each package contains its import boundary, consumer
type assertions, theorem-level axiom audit, recursive dependency closure and
source provenance.

| Source group | Count | Role |
|---|---:|---|
| `_vendor` | 269 modules | Pinned Methlib foundation sources |
| `MethbokeAddon` baseline | 71 accepted owned modules | Separately registered additions in [owned-sources.json](owned-sources.json) |
| Endpoint wrappers baseline | 71 accepted modules | Independently audited import boundaries |
| Accepted baseline compiled scope | 411 modules | Shared source closure, without duplicate foundation rebuilding |

| Package family | Exact role |
|---|---|
| MathlibAnalytic / MathlibFourier / MathlibODE | Pinned analysis, Fourier and ODE interfaces |
| QFB and physical foundation packages | Original eventual-tail contract, actual weak existence, trace uniqueness and physical realization |
| R0 packages | Actual finite-cap admission, comparison, velocity and normalized-pressure gluing |
| WFB packages | Actual local/maximal theory and finite full Fourier-budget continuation |
| EhrenfestScalar / EhrenfestCanonical / EhrenfestEscape | Scalar comparison, literal reciprocal drift and stopped threshold escape |
| Ehrenfest reference/error/forcing packages | Actual smooth-reference and finite-error estimates |
| [EhrenfestEventualEnstrophyBound](EhrenfestEventualEnstrophyBound/README.md) | Accepted E09.bound helper |
| [EhrenfestObstructionRoot](EhrenfestObstructionRoot/README.md) | Accepted exact conditional E10 root |

Preparation labels inside immutable endpoint manifests are not a replacement
for source-specific acceptance receipts. Acceptance applies to the exact source,
dependency, consumer and audit-policy identity recorded in the reviewed run.
This documentation amendment preserves those active proof and audit bytes; its
later commit is not represented as the tested SHA.

## Independent cutout export

An independently transferable full cutout is produced by:

```sh
python3 Material/ci/export_endpoint.py QFBRoot --output cutouts/QFBRoot --zip cutouts/QFBRoot.zip
```

Use the corresponding registered endpoint name for another package. The exported
directory includes the local dependency closure, compiler/dependency pins, exact
consumer audit, build driver and native `run.cmd`. Its only external source
dependency is the pinned public Mathlib dependency graph.

## Compiler and dependency identity

```text
Lean       = leanprover/lean4:v4.33.0
Mathlib    = db584cd6d46c92f209a44c0f1c829460d327499d
Methlib    = 96033dd69c994bec337a87369a6c27256e724980
```

`lake-manifest.json` preserves all nine exact public dependency revisions.
Vendor source identities are retained in `_vendor/source-manifest.json`.
No private Methlib checkout is needed during CI.

## External verification

Native Windows replay entrypoint:

```text
Material\run.cmd
Material\run.cmd --endpoint QFBRoot
```

The accepted evidence above is Linux evidence, not native-Windows evidence.
No local Lean, Lake, kernel, wrapper, subprocess or container execution is
permitted. Local work is restricted to reading, file preparation and
nonexecuting static inspection.

The external Linux workflow defaults to `binary_cache`. It restores compatible
dependency/project objects, validates receipt identities, rebuilds affected own
modules and executes every required audit freshly. Manual `backend=registry`
retains the GHCR path. Only an explicit current-run cache rejection can select
bounded recovery; proof, audit, static, publication and unknown failures preserve
the accepted baseline without selecting a cold rebuild.

1. Preserve the compiler, complete dependency lock, source and audit-policy
   identity. A cache label alone is insufficient.
2. Reuse compatible unchanged objects and schedule affected modules by the
   dependency graph. The accepted configuration uses two module workers and
   two Lean threads.
3. Run all configured exact consumer types and theorem-level axiom audits
   freshly for each new verification run.
4. Record cache class, restoration, compilation, audit and total time separately.
   Strict exact-cache measurements stop on a miss.
5. Publish verified caches/artifacts only after the complete required build and
   fresh audit pass. Preserve prior accepted objects and source-specific receipts.

Allowed theorem axioms are `propext`, `Classical.choice` and `Quot.sound`.
Missing or duplicate required reports, unknown axioms and `sorryAx` fail
acceptance. Static inspection and CI status alone are not theorem acceptance.
Missing official Mathlib objects do not authorize a Mathlib source rebuild.

The retained receipt covers the prior accepted baseline. The new family proof
and audit sources require fresh matching external evidence; a documentation-only
update alone would not require an identical rerun. See
[CI controls](ci/README.md) and the [registry guide](registry/README.md).

## Retained history

The previous detailed README, including earlier cold/warm observations, R0
failures and source-specific scope boundaries, is preserved
[verbatim](../audits/goal-transition-22431f/secondary/Material/README.md).
Earlier timing measurements describe their original source scopes and do not
predict current performance. Failed attempts remain retained in `audits/`.

The prior conditional Ehrenfest implication remains closed with its stopped-bound premise.
The current Fefferman-D family root remains open in this repository.
No unconditional stopped witness, full operator construction or full H2
Galerkin-convergence result is inferred from this acceptance.

