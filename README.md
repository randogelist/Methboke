# Methboke

## Current construction: forced L2 response and physical energy pairing

**Matching external verification is pending** for three new packages:

| Package | Prepared scope |
|---|---|
| `QFAHeatDuhamel` | Actual retarded integral, continuous zero trace, forcing-class invariance and exact time-L2 forcing bounds; 15 declarations |
| `QFAHeatDuhamelOperator` | Actual bounded map from the forcing Lp quotient to continuous L2 paths, norm at most sqrt(T), zero trace and representative compatibility; five declarations |
| `QFAHeatSpatialEnergy` | Actual H1 integration by parts, H1-H2 Laplacian pairing, bilinear H2 symmetry and negative-enstrophy identity; four theorems |

The batch has **24 declarations: 22 theorems and two definitions**, covered by
29 independent consumers. The expected complete run is **534 modules,
109 fresh package audits and 1,435 named reports**. Prepared source is not
A-tier acceptance. The generator acceptance below and all earlier scopes remain.

The response uses finite-window time-L2 spatial-L2 forcing. Forced maximal
regularity, the inhomogeneous derivative equation and nonlinear local theory
remain separate obligations. Steps 1 and 7 remain complete; step 3 is open.

## Accepted actual free-heat generator and equation from the initial trace

**Nine theorems are A-tier accepted at `809aadc6`**, with eleven
independent consumers, in [external run 44853804320](https://github.com/randogelist/Methboke/actions/runs/44853804320).
The complete run passed **528 modules, 106 fresh package audits and 1,411 unique
named type/axiom reports**, plus fresh QFB, complete publication and the final gate.
[Independent review](audits/material-809aadc6-qfa-heat-generator-accepted/independent-review.json) ·
[All nine theorem reports](audits/material-809aadc6-qfa-heat-generator-accepted/new-declaration-index.json) ·
[Exact derivation](R3_NSE/QFA/DERIVATIONS/HEAT_GENERATOR_CHAIN.txt).

For arbitrary actual physical H1 data and positive viscosity, `QFAHeatGenerator`
proves the strong L2 time derivative of the actual free-heat velocity at every
positive time. Its derivative is exactly viscosity times the physical Laplacian.
That derivative belongs to finite-window L2 in time and is Bochner integrable
down to zero. The integrated equation starts from the **original continuous
H1/L2 initial trace**. Its exact derivative-energy coefficient is **viscosity
divided by two**. No derivative or integrability witness is supplied as a premise.

The H2 trajectory's auxiliary value at zero is used only in integrals; it does
not replace the true initial velocity or assert an H2 initial trace.
**Step 3 remains open. Steps 1 and 7 remain the only completed checklist items.**
The next microscopic target is the actual L2 Duhamel response for finite-window
time-L2 spatial-L2 forcing: continuity, zero initial trace and the sqrt(T) bound
using the actual forcing Lp norm, together with the integral-of-norm bound.
Forced maximal regularity and nonlinear H1 theory follow as separate obligations.

The accepted 35-declaration heat-time layer and the conditional main-branch
FDSN_R3 receipt below are retained. General QFA/WFA, five G-parent gaps, M2/M3
and the D-family root remain open; P01-P08/M1 and the Fefferman D goal are unchanged.
No local Lean was executed.

## Accepted free-heat time-energy and all-window weighted budget

**35 declarations are A-tier accepted at `000c1bd9`: 32 theorems and three
definitions**, in [external run 44851575278](https://github.com/randogelist/Methboke/actions/runs/44851575278). The complete run
passed **526 modules, 105 fresh package audits and 1,402 unique named type/axiom
reports**, plus fresh standalone QFB, complete publication and the final gate.
The matching [independent review](audits/material-000c1bd9-qfa-heat-time-accepted/independent-review.json)
checks the exact source, full types and standard-only transitive axioms.

| Package | Accepted scope |
|---|---|
| `QFAHeatTrajectory` | 15 declarations: the actual positive-time H2 heat trajectory, physical semigroup agreement, H2 continuity away from zero and strong time measurability |
| `QFAHeatTimeEnergy` | 19 declarations: exact enstrophy dissipation, actual Laplacian square integrability and finite-window L2-time H2 membership with a quantitative bound |
| `QFAWeightedBudgetAllWindows` | One theorem: actual LH product integrability and the factor-one-quarter weighted bound for every finite T >= 0, including the empty zero window |

**Checklist step 7 is complete for every supplied actual LH path.** Steps 1
and 7 are complete. Step 3 now also has the accepted actual free-heat generator
and integrated equation described above; the forced response, maximal regularity
and nonlinear H1 theory remain open. General-data global LH existence is a
separate step-4 obligation.
The H2 trajectory's zero extension at nonpositive times makes no H2 initial
trace claim for arbitrary H1 data; the physical H1 heat flow retains its original trace.

[Exact construction chain](R3_NSE/QFA/DERIVATIONS/HEAT_TIME_ENERGY_CHAIN.txt) ·
[All 35 named declarations](audits/material-000c1bd9-qfa-heat-time-accepted/new-declaration-index.json).
Earlier failed attempts remain in the retained evidence and history registers.
The general QFA/WFA roots, five open NSE-A G-parent targets, P/M status and
Fefferman D project goal are unchanged. No local Lean was executed.

### Separate accepted main-branch FDSN_R3 result

Main source `572fd9ee`, [run 44848985720](https://github.com/randogelist/Methboke/actions/runs/44848985720),
has all **16 FDSN_R3 endpoints** accepted, including the original conditional
`Seed → Family` root. Its [retained independent evidence](audits/material-572fd9ee-fdsn-r3-accepted/independent-review.json)
records 548 modules, 137 fresh package audits and 1,320 named reports; the
FDSN_R3 scope comprises 493 declarations in 26 packages. This is explicitly
**main-branch provenance**. Seed existence, general QFA/WFA and the D-family
root remain open. Retaining this evidence neither imports FDSN_R3 into
AC-Integration nor changes the main branch or its proof scope.

## Earlier accepted restart, smoothing and zero-datum scopes

**Three native QFA layers are A-tier accepted at `ffbab0f5`**,
[external run 44847013775](https://github.com/randogelist/Methboke/actions/runs/44847013775). The complete run passed **520 modules,
102 fresh package audits and 1,367 named type/axiom reports**, plus standalone
QFB, publication and final acceptance. The new packages add **73 declarations:
53 theorems and 20 definitions/structures**. Only the approved standard axioms occur.

| Package | Accepted scope |
|---|---|
| `QFALHRestart` | Full physical restart of the same supplied LH path from its exact nonnegative energy-start trace, including translated momentum and all energy-class fields |
| `QFAHeatSmoothing` | Constructed actual positive-time H1-to-H2 heat map, native weak Hessians and quantitative Laplacian/H2 estimates |
| `QFAZeroDatum` | Exact physical root contract and complete zero-datum strict/closed QFA conclusion, including weak existence, every-path smooth tails, original-gradient energy equality and all future velocities |

**The general nonzero-data QFA theorem remains open.** Its cutoff is unchanged:
$8\|a\|_2^4/(27\pi^4\nu^5)$. Smooth pressure uses the explicit point gauge
$p(t,0)=0$. The new zero-datum result includes the closed cutoff at time zero.

[Exact acceptance](audits/material-ffbab0f5-qfa-accepted/independent-review.json) ·
[Full new-name register](R3_NSE/QFA/QFA_CLOSURE_A_TIER_PROGRESS.txt) ·
[Scoped mathematical chain](R3_NSE/QFA/DERIVATIONS/RESTART_HEAT_ZERO_CHAIN.txt).
No local Lean was executed. The project goal remains Fefferman D.

The next scoped construction is the **actual L2 Duhamel response** for
finite-window time-L2 spatial-L2 forcing: continuity, its zero initial trace,
the sqrt(T) bound using the actual time-L2 forcing norm and the integral-of-norm
bound. Forced maximal regularity, nonlinear H1 existence, general
LH existence, physical comparison, sharp spatial admission and small-product
continuation remain explicit general-data obligations.

## Earlier accepted NSE-A native basis

**Source `d403c235` is fully accepted**, [run 44837033211](https://github.com/randogelist/Methboke/actions/runs/44837033211):
**512 modules, 99 fresh package audits and 1,294 named type/axiom reports**,
plus the standalone QFB audit, publication and final acceptance. The six added
packages supply **307 declarations: 252 theorems and 55 definitions/instances**.
They construct the full stopped budgets and physical gauge, actual H2 and
Laplacian, real L2/H1 Leray projection, bounded real-even Fourier multipliers,
and strongly continuous heat semigroup. All 22 NSE-A scoped packages now
contain **596 accepted declarations**. Only the approved standard axioms occur.
**P01–P08 / M1 are complete** for supplied physical H1 paths. Canonical NSE
existence, M2/M3 and the five remaining G-parent targets stay open.

[Exact retained acceptance](audits/material-d403c235-nse-a-accepted/independent-review.json).
The general physical QFA and WFA roots remain open. The next nonlinear edges
are actual H1 local existence, global LH existence, weak–strong comparison,
sharp spatial admission and small-product continuation. No local Lean was run.

The project goal is **Fefferman D**: construct smooth periodic Navier–Stokes
initial data and an admissible smooth periodic force for which no global
smooth periodic velocity–pressure solution exists.

The selected route is **Fefferman_D_Family_obstruction**. It strengthens the
existence target to every positive viscosity and every finite configuration
of distinct torus sites, with zero initial velocity, bounded preterminal cell
energy, and local velocity blowup at all prescribed sites at time one. Taking
one site gives the intended obstruction; the literal all-order force-decay
adapter is an explicit formal obligation.

This working branch is `AC-Integration`; `main` remains the Fefferman-D program
branch. The [project context](GPT.txt) records both scopes. The
[prior goal documents](audits/goal-transition-fefferman-d/manifest.json)
retain the previous conditional Ehrenfest goal and its accepted evidence.

## Earlier accepted physical H1/Fourier/six-projector target

**G05 and P01–P07 are A-tier accepted at `09bcf251`**, [external run 44820225574](https://github.com/randogelist/Methboke/actions/runs/44820225574). All **496 modules, 93 fresh package audits and 987 named type/axiom reports** passed. The latest seven packages add **134 declarations: 116 theorems and 18 definitions**. Only standard axioms occur; publication and final acceptance passed. The original G05 physical H1/Fourier/six-projector scope is complete. G01, G02, G03, G04 and G06, the canonical NSE-A class root and universal budget finiteness remain open. No local Lean was executed.

[Six targets and remaining edges](R3_NSE/A-Regularity-class/SIX_GAP_A_TIER_TARGETS.txt) · [All accepted names](R3_NSE/A-Regularity-class/SIX_GAP_A_TIER_ACCEPTED_HELPERS.txt) · [Exact evidence](audits/material-09bcf251-nse-a-accepted/independent-review.json)

The construction now supplies actual real Fourier range, six real L2 and H1
orthogonal projections, derivative and native solenoidal preservation, and
physical gradient charges equal to the literal cone integrals with factor
$4\pi^2$. P07 supplies the exact pointwise factor-six comparison. The
small-product coefficient result is a separately scoped scalar helper.

Independent reviewed B-tier work develops the physical energy/enstrophy and
cutoff chain, the actual H2 graph and Hessian/Laplacian reconstruction, and the
full ENNReal stopped-window/gauge interface. The subsequently accepted stopped-budget packages supply the pathwise P08 layer;
its window and gauge statements use supplied H1 paths and do not require an
NSE existence theorem. The [cumulative derivation](R3_NSE/A-Regularity-class/NSE_A_A_TIER_STEPLIST_B_TIER.txt)
and [package/source assessment](R3_NSE/A-Regularity-class/SIX_GAP_PACKAGE_ASSESSMENT.txt)
record all hypotheses and remaining edges.

Prior accepted source `3dec32be` and its 155 names remain unchanged and are
rechecked by this full run. Those three earlier NSE-A batches contain 16 packages
and 289 accepted names:242 theorems and47 definitions/instances. The later
`d403c235` batch brings this separate NSE-A register to 22 packages and 596 names.

## AC-Integration: accepted native QFA foundations

**A-tier accepted at `afd67db4`**, [external run 44788963412](https://github.com/randogelist/Methboke/actions/runs/44788963412).
All 463 modules, 77 fresh package audits and 698 named type/axiom reports passed,
including 188 reports for the four new QFA packages. Publication and final
acceptance passed. The native additions comprise 35 public helper theorems and
19 contracts/definitions; only standard axioms occur. No local Lean was executed.

The integration supplies concrete whole-space energy-class contracts, weighted
energy and strong traces for supplied LH paths, half-window selection of actual
weak-gradient energy traces, and a Fourier spectral endpoint from distributional
derivative witnesses. The complete physical QFA/WFA roots remain open. The later
`ffbab0f5` batch constructs full supplied-path PDE restarts and the complete
zero-data tail and future conclusion. Spatial admissibility, general-data
weak/strong existence, continuation, comparison and the nonzero-data tails
remain open.

The [whole-space integration page](R3_NSE/QFA/README.md),
[accepted name register](R3_NSE/QFA/QFA_FOUNDATIONS_A_TIER.txt),
[exact receipt](audits/material-afd67db4-qfa-accepted/summary.json) and
[updated ten-step checklist](Temp-folder/QFA_QFB_10_STEP_CHECKLIST.md)
record the scope and remaining edges. The Fefferman-D goal, prior periodic
QFB/WFB conclusions and their original evidence remain preserved.

## NSE-A regularity class: finite six-charge budget

The [whole-space regularity class](R3_NSE/A-Regularity-class/README.md)
is registered at **B-tier**. A real solenoidal Schwartz datum belongs to the
class exactly when its canonical maximal strong solution has a finite full-window
integral of the sum of the six squared gradient charges. The six
projections are explicitly constructed from even Fourier sectors.

The [complete derivation](R3_NSE/A-Regularity-class/NSE_A_FINITE_CHARGE_CLASS_B_TIER.txt)
proves the factor-six comparison with squared enstrophy and records the existing
WFA equivalence to global canonical regularity, including the zero datum and
terminal endpoint. The [status record](R3_NSE/A-Regularity-class/STATUS.json)
keeps this analytic class characterization separate from the accepted native
foundations. Universal finiteness for every Schwartz datum remains open.
This registration adds no Lean declaration or new A-tier acceptance.

The [twenty-endpoint A-tier construction plan](R3_NSE/A-Regularity-class/A_TIER_STEPLIST.md)
now separates the pathwise six-charge theorem, actual canonical NSE
continuation, and the literal Fefferman-A solution-class bridge. It is a
B-tier step list with source anchors and explicit completion criteria;
the authorized construction has now reached P01–P08/M1 and G05 acceptance.
The canonical PDE/class obligations and M2/M3 remain open.

The [Lean gap and cutout collection](R3_NSE/A-Regularity-class/LEAN_CUTOUTS/README.md)
now supplies 51 exact reference blocks, complete pinned source snapshots and
[a ranked gap assessment](R3_NSE/A-Regularity-class/LEAN_CUTOUTS/GAPS.md).
The cumulative TXT references every cutout. Source acquisition narrows the
missing adapters and adds no native theorem or A-tier acceptance.

## NSE-A six-gap native construction

The [six closure targets](R3_NSE/A-Regularity-class/SIX_GAP_A_TIER_TARGETS.txt)
retain their original contracts. **G05 is complete**; G01,G02,G03,G04,G06
remain open. The [implementation and evidence register](R3_NSE/A-Regularity-class/SIX_GAP_IMPLEMENTATION_STATUS.json)
records 22 accepted packages and596 names, with the full named audits and all
historical failed attempts preserved. Reviewed B-tier chains identify the
remaining spatial, time-evolution and canonical-class constructions.

## Retained Fefferman-D implementation

The native family layers are in
[`Material/MethbokeAddon/FeffermanFamily/`](Material/MethbokeAddon/FeffermanFamily/):

| Source | Scope |
|---|---|
| `LocalBlowup.lean` | Quantitative local blowup, growth-sequence admission, compact-carrier localization and obstruction to continuous extension |
| `DisjointGerms.lean` | Finite disjoint closed carriers and local equality to one summand or zero, including spacetime |
| `FamilyContracts.lean` | Native forced NSE, periodic velocity and pressure, smooth compact-time force, distinct torus sites and exact family contracts |
| `GrowthSequence.lean` | Explicit growth-sequence selection from a speed-unboundedness hypothesis and compact localization |
| `CopyBlowup.lean` | Translation, recentering and positive parabolic transport of an assumed local blowup point |
| `LocalDifferential.lean` | Native operator locality, including the right time derivative at zero |
| `DisjointNSE.lean` | Conditional exact NSE and divergence equations for finite disjoint supported sums |

The new [FeffermanFamilyFoundation package](Material/FeffermanFamilyFoundation/README.md)
passed matching external verification at `77a64245`:
**28 helper theorems and 11 contract declarations**, standard axioms only.
[Run44655638162](https://github.com/randogelist/Methboke/actions/runs/44655638162) covered 415 modules,72 fresh package audits and 487 named
reports plus QFB. [Retained evidence](audits/material-77a64245-family/summary.json)
records the exact scope. The family witness and Fefferman-D root remain unproved.

The [T³ route](T3_NSE/D-Family-Obstruction/README.md),
[B-tier derivation](T3_NSE/D-Family-Obstruction/Fefferman_D_Family_obstruction_B_TIER.txt),
[source index](T3_NSE/D-Family-Obstruction/FEFFERMAN_C_D_FAMILY_OBSTRUCTION_INDEX.txt)
and [implementation ledger](T3_NSE/D-Family-Obstruction/IMPLEMENTATION_STATUS.json)
separate the mathematical construction from completed formal adapters.

The remaining native family route includes the compact literature seed and its
compatibility with this project, transformed-copy PDE and support identities,
finite packing, energy, force admission, periodization, smooth-force decay and
same-force comparison. The seed reference uses Lean `4.34.0-rc2`; it has not been imported
or newly verified under Methboke's `4.33.0` pin.

## Current build toward Fefferman D

The [direct endpoint](T3_NSE/D-Family-Obstruction/UpstreamSeed/README.md) is
prepared for isolated external verification of the pinned upstream periodic-D
proof. Its literal force and competitor contracts receive independent checks.
This 604-module route keeps its original Lean4.34.0-rc2 pin and leaves Material
at 4.33.0. It explicitly reuses the upstream proof; complete acceptance is pending.

Run 44663007873 completed compilation and fresh audits, but evidence upload excluded the hidden .fefferman-d-evidence directory and final acceptance failed. The workflow now includes hidden evidence files; a matching external rerun is required. No theorem, compiler pin or audit policy changed.

The [native assembly package](Material/FeffermanFamilyAssembly/README.md) is
accepted at `f19531bc`: **22 additional helper theorems and 1 predicate**.
[Run 44663707207](https://github.com/randogelist/Methboke/actions/runs/44663707207) passed 420 modules
(415 reused, 5 fresh), 73 fresh package audits, 510 named type/axiom reports
plus QFB and 183 controls, with standard axioms only.
[Matching evidence](audits/material-f19531bc-assembly/summary.json) and the
[A-tier register](T3_NSE/D-Family-Obstruction/FEFFERMAN_D_ASSEMBLY_A_TIER.txt)
record the exact accepted scope. The native family total is **50 helper theorems
and 12 contract/predicate declarations**. Geometric blowup transport does not
prove transformed-copy PDE identities. The full family witness remains open.
The [first failed attempt](audits/material-dd0e355-assembly-failure/summary.json)
is retained as superseded history.

## Accepted foundations

The previous exact conditional theorem
`ν > 0 → StoppedCommutatorBound ν → ¬ NSE_B ν` remains accepted with its
explicit stopped-bound hypothesis. Its witness remains unproved.
[Run 44645541035](https://github.com/randogelist/Methboke/actions/runs/44645541035)
at `3335bbc52ec58fc080577143863b9ad5e4cc3edb` freshly verified the comment-only
source refresh: 411 modules, 71 packages, 448 named audits plus QFB, standard
axioms only. [Retained evidence](audits/material-3335bbc5-comments/summary.json)
and the [A-tier register](T3_NSE/B-Heisenberg-Obstruction/StoppedCommutatorBound/EHRENFEST_OBSTRUCTION_A_TIER.txt) preserve the exact scope.
E09.bound is the actual-front eventual enstrophy helper; full H2 convergence,
operator realization and the stopped-bound witness remain separately open.

**Weak_Fourierman_B** remains accepted in its finite full squared Fourier-budget
scope at `fdb515d8`, [run 44566880192](https://github.com/randogelist/Methboke/actions/runs/44566880192).
The budget remains a hypothesis. R0 retains its actual finite-cap premise;
QFB retains eventual-tail energy and post-cutoff uniqueness. These unforced
results are not substituted for forced same-force comparison.

## Repository map

`T3_NSE` and `R3_NSE` are ordinary domain folders. `Material/` retains the
shared build paths. The [relocation map](REORGANIZATION_MAP.json) preserves
the previous research-file locations.

| Path | Purpose |
|---|---|
| [GPT.txt](GPT.txt) | Branch preparation scope, retained goal, exact contracts and formal obligations |
| [Temp-folder](Temp-folder/README.md) | QFA/WFA source and evidence staging; no new A-tier acceptance |
| [INDEX-WORTHY.txt](INDEX-WORTHY.txt) | Substantiated results with source-specific scope and evidence |
| [SOURCE_STATUS.json](SOURCE_STATUS.json) | Goal, implementation and accepted-evidence identities |
| [T3_NSE](T3_NSE/README.md) / [R3_NSE](R3_NSE/README.md) | Periodic programs and reserved whole-space work |
| [NSE-A regularity class](R3_NSE/A-Regularity-class/README.md) | B-tier finite six-charge class and datumwise global-regularity equivalence |
| [T3_NSE/D-Family-Obstruction](T3_NSE/D-Family-Obstruction/README.md) | Current periodic-family route and ledger |
| [Material](Material/README.md) | Native sources, endpoint packages and complete audits |
| [Ehrenfest package](T3_NSE/B-Heisenberg-Obstruction/StoppedCommutatorBound/PREPRINT_FORMALISATION/README.md) | Preserved conditional proof and stronger open operator milestones |
| [WFB preprint](T3_NSE/B-Regularity-class/WFB/PAPER_PREPRINT_PDF/WFB_FOURIER_BUDGET_PREPRINT.pdf) | Accepted finite-budget result and exposition |

## Verification

Local Lean, Lake invoking Lean and local kernel audits are forbidden. The pin
remains `leanprover/lean4:v4.33.0` with Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. Dependency locks, vendor sources and
all existing audits are preserved.

The existing [Material workflow](.github/workflows/material.yml) restores
compatible accepted objects, compiles affected owned modules, and runs every
required exact-type and theorem-axiom audit freshly. New source preparation
or a green workflow alone is not A-tier. Matching evidence must cover the
precise statement and allow only `propext`, `Classical.choice` and `Quot.sound`.
Missing official Mathlib objects do not authorize a source rebuild.


## Further NSE-A native work

The accepted six-target register now marks G05 complete. The remaining five
parents require native local/maximal NSE, sharp spatial admission, physical
energy/enstrophy evolution, the literal smooth class bridge and the canonical
full-budget equivalence. Reviewed B-tier derivations are retained in
[R3_NSE/A-Regularity-class/DERIVATIONS](R3_NSE/A-Regularity-class/DERIVATIONS/).
The exact failed attempts remain in the implementation history and evidence
archives; they are superseded by the matching current acceptance above.
