# Methboke

The project goal is **Fefferman D**: construct smooth periodic Navier–Stokes
initial data and an admissible smooth periodic force for which no global
smooth periodic velocity–pressure solution exists.

The current local theorem is **FEFFERMAN_D_SPECTRAL_NONRIGIDITY (FDSN)** on the unit three-torus: an exact admissible preterminal seed produces a localized phase family preserving modal powers while separating translation classes and projected force histories. The [canonical proof and construction checklist](T3_NSE/D-Family-Obstruction/FDSN/FDSN_B_TIER.txt) and [implementation ledger](T3_NSE/D-Family-Obstruction/FDSN/IMPLEMENTATION_STATUS.json) track this single local target. The initial phase and bump packages passed [external CI44801643103](https://github.com/randogelist/Methboke/actions/runs/44801643103): 21 exact named declarations, standard axioms only. The full construction and canonical root are now prepared in 36 pending packages (296 named declarations); full FDSN remains externally unverified.

The preserved prescribed-site route is **Fefferman_D_Family_obstruction**. It strengthens the
existence target to every positive viscosity and every finite configuration
of distinct torus sites, with zero initial velocity, bounded preterminal cell
energy, and local velocity blowup at all prescribed sites at time one. Taking
one site gives the intended obstruction. The cumulative B-tier construction is
complete relative to the pinned compact seed; its native Lean family theorem
and literal all-order force-decay adapter remain formal obligations.

The working branch is `main`. The [project context](GPT.txt) records the exact
scope. The [prior goal documents](audits/goal-transition-fefferman-d/manifest.json)
retain the previous conditional Ehrenfest goal and its accepted evidence.

## Current implementation

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
records the exact scope. This package alone supplies no family witness or D root;
the separate direct-D endpoint has since been accepted as recorded below.

The [T³ route](T3_NSE/D-Family-Obstruction/README.md),
[B-tier derivation](T3_NSE/D-Family-Obstruction/Fefferman_D_Family_obstruction_B_TIER.txt),
[source index](T3_NSE/D-Family-Obstruction/FEFFERMAN_C_D_FAMILY_OBSTRUCTION_INDEX.txt)
and [implementation ledger](T3_NSE/D-Family-Obstruction/IMPLEMENTATION_STATUS.json)
separate the mathematical construction from completed formal adapters.

The cumulative TXT is now **version 1.6**. It derives prescribed-site blowup,
arbitrarily small energy, dissipation and `L1_t L2_x` forcing, spatial localization,
an arbitrarily short force window around time one, and finite mixed-force budgets
when `3/p + 2/q > 3`. It also records why zero force cannot retain this zero-data
blowup family. These are **B-tier** conclusions, not new Lean acceptance.
The preferred route periodizes each compressed copy before torus translation;
the final same-force comparison needs no generic-radius candidate wrapper.

The remaining native family route includes the compact literature seed and its
compatibility with this project, transformed-copy PDE and support identities,
finite packing, energy, force admission, periodization, smooth-force decay and
same-force comparison. The seed reference uses Lean `4.34.0-rc2`; it has not been imported
or newly verified under Methboke's `4.33.0` pin.

## Current build toward Fefferman D

The [direct endpoint](T3_NSE/D-Family-Obstruction/UpstreamSeed/README.md)
`Methboke.FeffermanD.Fefferman_D` is **A-tier accepted** at `66a5292`,
[run 44768857811](https://github.com/randogelist/Methboke/actions/runs/44768857811).
The matching run passed 605 modules, independent literal-contract checks and
fresh named axiom audits, with standard axioms only; evidence retention,
cache publication and final acceptance passed. The
[acceptance record](T3_NSE/D-Family-Obstruction/UpstreamSeed/ACCEPTANCE.json)
pins the source and artifact. It explicitly reuses the upstream proof at
Lean 4.34.0-rc2 and leaves native Material at 4.33.0.
The earlier evidence-retention failure in run 44663007873 is superseded.
This direct existential theorem does not establish the stronger family root.

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
| [GPT.txt](GPT.txt) | Current goal, exact contracts, derivation and next formal obligations |
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


The second FDSN run stopped at a finite-sum congruence elaboration error. Its statement-preserving repair is prepared; [failure evidence](audits/fdsn-1cb76bc0-failed/summary.json) is retained.

The next full-chain candidate includes the repaired localized spacetime wrapper and the actual active-triad, residual-force, smallness and separation arguments. [The preceding failed-run evidence](audits/fdsn-dbbfe1e9-failed/summary.json) is retained; it gives no new acceptance.

FDSN verification repair after run44805483799: Normalize pointwise functions and native vector/slice coercions, replace the reserved lambda token with an alpha-equivalent identifier, and repair one malformed audit consumer; add a separate physical Leray interpretation adapter. [Failure record](audits/fdsn-25c5a4e3-failed/summary.json).

FDSN verification repair after run44806525675: Resolve the finite-norm estimate elaboration, explicit zero-velocity germs, inequality addition orientation and pointwise coefficient coercions; include the same-witness physical presentation corollary. [Failure record](audits/fdsn-bfddc915-failed/summary.json).

FDSN verification repair after run44807597711: Make residual smoothness subterms explicit with a scoped elaboration allowance, and normalize subtraction in the physical Leray coefficient identity. All theorem contracts are unchanged. [Failure record](audits/fdsn-38dd6ec5-failed/summary.json).

FDSN verification repair after run44808681563: Specify the exact inner and outer maps in both joint residual derivative compositions; theorem statements and audit consumers unchanged. [Failure record](audits/fdsn-6f02f8b7-failed/summary.json).

FDSN verification repair after run44809750811: Normalize the actual correction value in the initial-time vanishing-germ equality before rewriting; one proof line changed, all theorem contracts preserved. [Failure record](audits/fdsn-fe0ba0f3-failed/summary.json).
