# Methboke

## External compilation repair

[Run 44829344090](https://github.com/randogelist/Methboke/actions/runs/44829344090)
at source `6b1e654a` passed 506 of 512 scheduled modules. The real L2/H1 heat
semigroup now compiles. Two failures remain: kernel reduction of the H2
sigma-inclusion value theorem, and an explicit zero-function reduction in
LerayH1. Four dependents were blocked. The candidate repair factors the H2
inclusion through a generic proved submodule isometry and normalizes the
remaining function zero. Public statements and every audit are unchanged.
All 99 fresh package audits, 1,294 named reports, publication and final
acceptance remain required. The last accepted source remains `09bcf251`.
No new A-tier acceptance follows from these partial results.

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

## AC-Integration: accepted physical H1/Fourier/six-projector target

**G05 and P01–P07 are A-tier accepted at `09bcf251`**, [external run 44820225574](https://github.com/randogelist/Methboke/actions/runs/44820225574). All **496 modules, 93 fresh package audits and 987 named type/axiom reports** passed. The latest seven packages add **134 declarations: 116 theorems and 18 definitions**. Only standard axioms occur; publication and final acceptance passed. The original G05 physical H1/Fourier/six-projector scope is complete. G01, G02, G03, G04 and G06, the canonical NSE-A class root and universal budget finiteness remain open. No local Lean was executed.

[Six targets and remaining edges](R3_NSE/A-Regularity-class/SIX_GAP_A_TIER_TARGETS.txt) · [All accepted names](R3_NSE/A-Regularity-class/SIX_GAP_A_TIER_ACCEPTED_HELPERS.txt) · [Exact evidence](audits/material-09bcf251-nse-a-accepted/independent-review.json)

The construction now supplies actual real Fourier range, six real L2 and H1
orthogonal projections, derivative and native solenoidal preservation, and
physical gradient charges equal to the literal cone integrals with factor
$4\pi^2$. P07 supplies the exact pointwise factor-six comparison. The
small-product coefficient result is a separately scoped scalar helper.

Independent reviewed B-tier work develops the physical energy/enstrophy and
cutoff chain, the actual H2 graph and Hessian/Laplacian reconstruction, and the
full ENNReal stopped-window/gauge interface. The next native endpoint is P08;
its window and gauge statements use supplied H1 paths and do not require an
NSE existence theorem. The [cumulative derivation](R3_NSE/A-Regularity-class/NSE_A_A_TIER_STEPLIST_B_TIER.txt)
and [package/source assessment](R3_NSE/A-Regularity-class/SIX_GAP_PACKAGE_ASSESSMENT.txt)
record all hypotheses and remaining edges.

Prior accepted source `3dec32be` and its 155 names remain unchanged and are
rechecked by this full run. Across the three NSE-A batches, 16 packages contain
289 accepted names:242 theorems and47 definitions/instances.

## AC-Integration: accepted native QFA foundations

**A-tier accepted at `afd67db4`**, [external run 44788963412](https://github.com/randogelist/Methboke/actions/runs/44788963412).
All 463 modules, 77 fresh package audits and 698 named type/axiom reports passed,
including 188 reports for the four new QFA packages. Publication and final
acceptance passed. The native additions comprise 35 public helper theorems and
19 contracts/definitions; only standard axioms occur. No local Lean was executed.

The integration supplies concrete whole-space energy-class contracts, weighted
energy and strong traces for supplied LH paths, half-window selection of actual
weak-gradient energy traces, and a Fourier spectral endpoint from distributional
derivative witnesses. The complete physical QFA/WFA roots remain open: spatial
admissibility, weak/strong existence, continuation, full PDE restarts, comparison,
smooth tails and future uniqueness still require construction.

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
the authorized construction has now reached original P01–P07/G05 acceptance.
The next native step is P08; later canonical PDE/class obligations remain open.

The [Lean gap and cutout collection](R3_NSE/A-Regularity-class/LEAN_CUTOUTS/README.md)
now supplies 51 exact reference blocks, complete pinned source snapshots and
[a ranked gap assessment](R3_NSE/A-Regularity-class/LEAN_CUTOUTS/GAPS.md).
The cumulative TXT references every cutout. Source acquisition narrows the
missing adapters and adds no native theorem or A-tier acceptance.

## NSE-A six-gap native construction

The [six closure targets](R3_NSE/A-Regularity-class/SIX_GAP_A_TIER_TARGETS.txt)
retain their original contracts. **G05 is complete**; G01,G02,G03,G04,G06
remain open. The [implementation and evidence register](R3_NSE/A-Regularity-class/SIX_GAP_IMPLEMENTATION_STATUS.json)
records 16 accepted packages and289 names, with the full named audits and all
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
