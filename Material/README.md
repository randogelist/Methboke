# Material

## AC-Integration into main: prepared candidate

The immediate task on `integration/ac-into-main` combines main
`4a609ea634ec4a5ff846049b9dc12b40b5f1a702` with AC-Integration
`000c1bd9baded808b79a04b7f666cacabce64939`. The project goal remains
**Fefferman D**. No new mathematical goal is selected by this integration.

**The combined candidate is pending matching external verification.** Its
expected scope is **654 modules, 169 fresh package audits, 2,212 named
type/axiom reports and the original QFB cutout**. Existing source-specific
acceptances below are retained. See the [integration record](../integration/AC_INTO_MAIN/README.md),
[status](../integration/AC_INTO_MAIN/INTEGRATION_STATUS.json) and
[preservation manifest](../integration/AC_INTO_MAIN/PRESERVATION_MANIFEST.json).

## Whole-space FDSN_R3

Status: **A-tier accepted at `572fd9ee`**. The [FDSNR3Main package](FDSNR3Main/README.md)
contains the canonical conditional theorem
`MethbokeAddon.FDSNR3.FDSN_R3 : Seed ν T u p F → Family ν T u p F`.
The original seed hypotheses and the complete common-witness family contract
are retained. The root assembles all sixteen endpoint obligations.

For every regular start time `s`, the velocity and force corrections share a
compact temporal carrier inside a later interval strictly before `T`, with
parameter range `|λ| < π / 4`.
The family realizes the actual whole-space NSE with the same viscosity, initial data
and pressure; preserves all helical powers and a common low-frequency
neighborhood; separates distinct parameters from spatial translations at one
common observation time; separates their actual physical projected forces;
and gives all weighted mixed-derivative bounds linear in `|λ|`.
The same witnesses have exact terminal-tail agreement, equal energy and
dissipation histories, and the original compact-local blowup. The
time-integrated dissipation equality and the fixed-frame scalar interpretation
of helical power are separately audited supplements.

The root is conditional on the original `Seed`; it does not construct a singular
seed. Forces vary with the parameter, so this is not a same-force nonuniqueness
theorem. Force support is compact in positive time, with rapid spatial decay.

Exact source: [`572fd9ee69a6b641f435cbfb2ef74e034809c583`](https://github.com/randogelist/Methboke/tree/572fd9ee69a6b641f435cbfb2ef74e034809c583);
[external run 44848985720](https://github.com/randogelist/Methboke/actions/runs/44848985720);
[retained evidence](../audits/fdsn-r3-572fd9ee-accepted/summary.json).
The run passed **548 modules (502 reused, 46 fresh), 137 fresh package audits,
1,320 named type/axiom reports and the independent cutout verification**.
Only `propext`, `Classical.choice` and `Quot.sound` occurred in the accepted
axiom reports. The **26 FDSNR3 packages contain 493 named declarations**;
the sixteen-endpoint chain also reuses `FDSNBump` and `FDSNResidualForce`.
Workflow publication, the required gate and final Material acceptance passed.
The retained artifact is `14684049987`, with SHA-256
`320d05ae62963c329de38c4c570abef1a5e947e98dfe32ad2e3be43e78f76243`.
Acceptance applies to the tested source and independent consumer identity
recorded in that receipt.

## Retained whole-space QFA and NSE-A scopes

The incoming branch contributes the [QFA foundations](../R3_NSE/QFA/README.md)
and [NSE-A finite-charge program](../R3_NSE/A-Regularity-class/README.md).
Their accepted helper scopes remain attached to their original source receipts:

| Tested source / run | Retained scope |
|---|---|
| `afd67db4` / [44788963412](https://github.com/randogelist/Methboke/actions/runs/44788963412) | Recovered QFA sources and native whole-space energy, trace, finite-window and spectral foundations; 188 added named reports |
| `09bcf251` / [44820225574](https://github.com/randogelist/Methboke/actions/runs/44820225574) | G05 and P01–P07; cumulative 289 construction declarations |
| `d403c235` / [44837033211](https://github.com/randogelist/Methboke/actions/runs/44837033211) | Full stopped budgets and gauge, physical H2, real Leray and even multipliers, and the real heat semigroup; cumulative 596 construction declarations in 22 packages |
| `ffbab0f5` / [44847013775](https://github.com/randogelist/Methboke/actions/runs/44847013775) | Supplied-path LH restart, positive-time physical H1-to-H2 heat smoothing, the exact physical QFA contract and complete zero-datum branch; 73 additional declarations |
| `000c1bd9` / [44851575278](https://github.com/randogelist/Methboke/actions/runs/44851575278) | Actual positive-time H2 heat trajectory, exact free-heat enstrophy-dissipation identity, finite-window L2-time H2 membership and all-window weighted budget; 35 additional declarations |

The incoming head `000c1bd9baded808b79a04b7f666cacabce64939` is independently
accepted for its exact source scope: **526 modules (520 reused, 6 fresh), 105 fresh
package audits, 1,402 named type/axiom reports and the original cutout**.
Publication and final acceptance passed; only standard axioms occurred.
The [acceptance record](../audits/material-000c1bd9-qfa-accepted/summary.json)
and [independent review](../audits/material-000c1bd9-qfa-accepted/independent-review.json)
retain that evidence. Its H2 heat trajectory is zero-extended at nonpositive
times; it makes no H2 initial-trace claim for arbitrary H1 input. That run does
not verify this combined candidate. Source-specific details and earlier failures
remain in the [QFA status](../R3_NSE/QFA/INTEGRATION_STATUS.json) and
[NSE-A implementation history](../R3_NSE/A-Regularity-class/SIX_GAP_IMPLEMENTATION_STATUS.json).

The general physical QFA and WFA roots, canonical NSE-A class theorem and
universal finite-budget membership remain open. The B-tier finite-charge
class equivalence and accepted conditional or zero-datum results retain their
stated hypotheses and scopes.

## Retained periodic FDSN

The canonical T3 FDSN theorem and physical presentation remain accepted at
`87ab6b4cfc4a81a1fb6c8e37bb6d5caf3972b1ef`,
[run 44811785125](https://github.com/randogelist/Methboke/actions/runs/44811785125),
with 317 named declarations. The [exact receipt](../audits/fdsn-87ab6b4c-accepted/summary.json)
and [implementation ledger](../T3_NSE/D-Family-Obstruction/FDSN/IMPLEMENTATION_STATUS.json)
retain the original conditional Seed-to-Family scope.

## Earlier finite periodic family work

The finite periodic forced-family route toward **Fefferman D** remains
separately tracked. The first [foundation package](FeffermanFamilyFoundation/README.md) adds
28 local blowup, disjoint-carrier and native contract helper theorems and 11
contract declarations, accepted at 77a64245 by [external run 44655638162](https://github.com/randogelist/Methboke/actions/runs/44655638162).
The prescribed-site periodic D-family root remains unproved; see
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

The earlier `f19531bc` native verification passed 420 modules (415 reused, 5 fresh),
73 fresh package audits, 510 named type/axiom reports plus QFB and 183 controls,
using only standard axioms. See the [evidence](../audits/material-f19531bc-assembly/summary.json)
and [A-tier register](../T3_NSE/D-Family-Obstruction/FEFFERMAN_D_ASSEMBLY_A_TIER.txt).
The separate direct Fefferman-D endpoint is already A-tier accepted at
`66a529248d3198ed70dc5489d82868bc33a37796` by
[run 44768857811](https://github.com/randogelist/Methboke/actions/runs/44768857811);
its [accepted record](../T3_NSE/D-Family-Obstruction/UpstreamSeed/ACCEPTANCE.json)
retains that source and artifact identity. It uses its own 4.34rc2 pin;
Material retains 4.33.0. That earlier acceptance is not a new result of
the FDSN_R3 run.

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

The combined [endpoint registry](endpoints.json) is prepared for **169 packages
and 2,212 named declaration requests**, including the 26 FDSNR3 packages and the
incoming QFA/NSE-A scopes. These are the required integration verification counts;
they are not a completed combined run. Each package contains its import boundary,
consumer type assertions, theorem-level axiom audit, recursive dependency closure
and source provenance.

| Source group | Count | Role |
|---|---:|---|
| `_vendor` | 302 active modules from 304 retained sources | Pinned Methlib foundation sources; two original QFA sources remain inactive |
| `MethbokeAddon` | 183 owned modules | Separately registered additions in [owned-sources.json](owned-sources.json) |
| Endpoint wrappers | 169 modules | Independently audited import boundaries |
| Required integration build scope | 654 modules | Union of registered source closures; matching cached verification pending |

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
| [FDSNR3Main and the 25 supporting FDSNR3 packages](FDSNR3Main/README.md) | Conditional whole-space Seed-to-Family root; 493 named declarations, all sixteen endpoint obligations, fixed-frame and integrated-dissipation supplements |
| QFA recovered/native, NSE-A physical and heat packages | Retained source-specific whole-space helper scopes; general physical roots remain open |

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
The additional QFA vendor source pin is
`53b2318c2b586137b6db74c4d3a41bb0b964b2d8`; existing vendor bytes and
the native dependency lock are retained. No private Methlib checkout is needed during CI.

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
   two Lean threads. The existing cache transport selects one passed
   project snapshot; integration does not promise a union of branch caches or
   zero recompilation.
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

The [FDSN_R3 receipt](../audits/fdsn-r3-572fd9ee-accepted/summary.json) records the exact
`572fd9ee69a6b641f435cbfb2ef74e034809c583` source and audit identity. The `f19531bc`
receipt remains evidence for its earlier scope. Later documentation-only
updates preserve the tested proof and audit bytes and are not represented
as the tested revision. See
[CI controls](ci/README.md) and the [registry guide](registry/README.md).

## Retained history

The previous detailed README, including earlier cold/warm observations, R0
failures and source-specific scope boundaries, is preserved
[verbatim](../audits/goal-transition-22431f/secondary/Material/README.md).
Earlier timing measurements describe their original source scopes and do not
predict current performance. Failed attempts remain retained in `audits/`.

The prior conditional Ehrenfest implication remains closed with its stopped-bound premise.
The separately tracked prescribed-site periodic Fefferman-D family root remains open.
No unconditional stopped witness, full operator construction or full H2
Galerkin-convergence result is inferred from this acceptance.

