# Material

## External compilation repair

[Run 44826537985](https://github.com/randogelist/Methboke/actions/runs/44826537985)
at source `e6a233aa` passed 499 of 512 scheduled modules. Four newly prepared
sources failed elaboration and nine dependents were blocked. The retry adds an
explicit H1 import, makes bounded Fourier-isometry conversions and pointwise
coercions explicit, and corrects the fourth-power rewrite. Public statements
and independent consumers are unchanged. All 99 package audits, 1,294 named
reports, publication and final acceptance remain required. No new A-tier
acceptance follows from this attempt.


## Current candidate: H2, Leray and real multipliers

The next external candidate adds **202 declarations** in four packages:
the actual closed H2 graph and its exact Hessian–Laplacian norm identity;
the constructed real Leray projection and its native L2/H1 solenoidal range;
bounded real even Fourier multipliers with actual weak-gradient transport;
and the exact real L2/H1 heat semigroup with contraction and strong continuity.
It also repairs the missing `NNReal` notation scope exposed by
[the first stopped-budget run](https://github.com/randogelist/Methboke/actions/runs/44824925503).
The combined candidate requires **512 modules, 99 fresh package audits and
1294 named reports**. The 307 additions across these two batches are pending
matching external verification. The full canonical NSE-A theorem remains open.


## Active construction: full stopped budgets and gauge

The selected scoped goal is **`NSE_A_FINITE_CHARGE_IFF_GLOBAL`**. The next
candidate adds **105 declarations: 91 theorems and 14 definitions**, in
`QFAStoppedBudget` and `QFAPhysicalStoppedGauge`. It supplies the actual finite
observation window, complete endpoint budget limits including infinity,
physical/Fourier normalization, fourth-root gauge and integer sublevels.
These additions are **prepared pending matching external verification**.
The new registry contains 95 packages and 1092 named reports; the previously
accepted G05/P01–P07 proof and audit bytes are preserved.

The native H2, real Leray, local solution, sharp spatial estimate, evolution,
continuation and literal solution-category layers remain separate obligations.
The canonical class theorem and universal budget finiteness remain open.


## Current accepted NSE-A tranche

**G05 and P01–P07 are A-tier accepted at `09bcf251`**, [external run 44820225574](https://github.com/randogelist/Methboke/actions/runs/44820225574). All **496 modules, 93 fresh package audits and 987 named type/axiom reports** passed. The latest seven packages add **134 declarations: 116 theorems and 18 definitions**. Only standard axioms occur; publication and final acceptance passed. The original G05 physical H1/Fourier/six-projector scope is complete. G01, G02, G03, G04 and G06, the canonical NSE-A class root and universal budget finiteness remain open. No local Lean was executed.

The tested source, audit, endpoint and closure bytes are retained unchanged. Original preparation labels in those manifests are historical; acceptance is recorded in [the current scope register](../R3_NSE/A-Regularity-class/SIX_GAP_A_TIER_ACCEPTED_HELPERS.txt).

The current goal is **Fefferman D**, through the finite periodic forced-family
route. The first [foundation package](FeffermanFamilyFoundation/README.md) adds
28 local blowup, disjoint-carrier and native contract helper theorems and 11
contract declarations, accepted at 77a64245 by [external run 44655638162](https://github.com/randogelist/Methboke/actions/runs/44655638162).
The complete D family root remains unproved; see
the [implementation ledger](../T3_NSE/D-Family-Obstruction/IMPLEMENTATION_STATUS.json).

The [FeffermanFamilyAssembly package](FeffermanFamilyAssembly/README.md) adds
**22 accepted helper theorems and 1 predicate** at `f19531bc`, verified by
[run 44663707207](https://github.com/randogelist/Methboke/actions/runs/44663707207). The native family total is
**50 helper theorems and 12 contract/predicate declarations**. Accepted scope:
growth selection and compact localization, geometric positive parabolic blowup
transport, native operator locality including time zero, and conditional exact
finite-disjoint-sum NSE assembly. Transformed-copy PDE identities, seed admission,
packing, energy, force admission, periodization and same-force comparison remain
open for the family route.

The complete native verification passed 420 modules (415 reused, 5 fresh),
73 fresh package audits, 510 named type/axiom reports plus QFB and 183 controls,
using only standard axioms. See the [evidence](../audits/material-f19531bc-assembly/summary.json)
and [A-tier register](../T3_NSE/D-Family-Obstruction/FEFFERMAN_D_ASSEMBLY_A_TIER.txt).
The direct Fefferman-D upstream proof remains pending separate verification under
its own 4.34rc2 pin; Material retains 4.33.0.

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

The [endpoint registry](endpoints.json) contains **99 registered packages** and
**1294 named reports**, including six pending packages with307 new names. Each package records its exact import boundary,
independent full-type consumers, named axiom audit and recursive source closure.

| Source group | Count | Role |
|---|---:|---|
| `_vendor` | 302 compiled modules | Selected from 304 tracked pinned Methlib foundation sources |
| `MethbokeAddon` | 111 modules | Owned additions in [owned-sources.json](owned-sources.json) |
| Endpoint wrappers | 99 modules | Independently audited import boundaries |
| Accepted full run | 496 modules | Exact compiled closure |

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
| [FeffermanFamilyFoundation](FeffermanFamilyFoundation/README.md) | Accepted local blowup, disjoint-germ and native-contract foundations |
| [FeffermanFamilyAssembly](FeffermanFamilyAssembly/README.md) | Accepted growth extraction, geometric transport and conditional native disjoint PDE assembly |

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

The retained f19531bc receipt covers the current accepted native source and
audit scope. Later documentation-only updates preserve that tested identity
and do not require an identical rerun. See
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


## NSE-A accepted construction batches

The first two batches contribute nine packages and155 names, accepted at
3dec32be/run44810272232 and rechecked by the current full run. The third batch
adds seven packages and134 names, completing the original G05 and P04–P07
scopes. Across all three batches there are289 accepted names. The
[exact scope register](../R3_NSE/A-Regularity-class/SIX_GAP_A_TIER_ACCEPTED_HELPERS.txt)
and [implementation history](../R3_NSE/A-Regularity-class/SIX_GAP_IMPLEMENTATION_STATUS.json)
retain all source/type/axiom identities and earlier attempt outcomes.
