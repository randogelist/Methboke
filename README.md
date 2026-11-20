# Methboke

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

## AC-Integration: native QFA foundations

The user authorized integrating the reviewed [ten-step QFA/QFB plan](Temp-folder/QFA_QFB_10_STEP_CHECKLIST.md)
into the native build and obtaining matching cached external verification.
The [whole-space integration page](R3_NSE/QFA/README.md) records the exact
scope and the [integration status](R3_NSE/QFA/INTEGRATION_STATUS.json).

The integration adds exact recovered QFA sources and new whole-space
contract, weighted-energy, trace and safe-cutoff helpers. The finite window
selects an actual weak-gradient energy start strictly before its cutoff and
retains a half-window measure estimate. The scalar Sobolev parameter remains
explicit. Physical weak/strong existence, continuation, comparison, sharp
spatial admissibility and the complete QFA/WFA roots remain open.

**Current status: prepared, pending matching external compilation and fresh
exact-type/axiom audits.** The standard native workflow now includes this
branch. Its pins, lockfile, lakefile, drivers and verification policies are
unchanged. Existing periodic QFB remains the accepted reference.

[Staged archives](Temp-folder/README.md), the [source anchor register](Temp-folder/anchors/QFA_QFB_ANCHOR_REGISTER.md)
and [historical evidence review](Temp-folder/anchors/SOURCE_REVIEW.json)
preserve the recovery record. The Fefferman-D main goal and all its existing
proof/evidence statuses retain their original scope.

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
