# Methboke

## Current project goals

1. WFA
2. WFB
3. QFA
4. QFB
5. SINGULAR-PREMISE OBSTRUCT R3
6. SIGNULAR-PREMISE OBSTRUCT T3

| Domain | Goals |
|---|---|
| $\mathbb R^3$ | **WFA**, **QFA**, **SINGULAR-PREMISE OBSTRUCT R3** |
| $\mathbb T^3$ | **WFB**, **QFB**, **SIGNULAR-PREMISE OBSTRUCT T3** |

This latest six-goal declaration supersedes the earlier configurations. Existing
results, explicit hypotheses and source-specific evidence retain their status.

### Current state and six parallel theorem CI stages

[Theorem-goal CI](.github/workflows/theorem-goals.yml) and its
[goal manifest](Material/ci/theorem-goals.json) configure one stage per goal:

| Goal | Current state | Stage | Mathematical scope |
|---|---|---|---|
| **WFA** | `!=` | Dummy/pending | B-tier implication from a finite full Fourier budget established; complete general Lean root pending |
| **WFB** | `!!!!` | Real exact-type and axiom audits | Exact WFB implication closed; all WFB-01 through WFB-10 accepted, with the finite full Fourier budget retained as a stated hypothesis |
| **QFA** | `!=` | Dummy/pending | B-tier tail theorem for general solenoidal $L^2$ data established; complete general Lean root pending |
| **QFB** | `!!!!` | Real exact-root and standalone-cutout audits | Closed in its exact post-cutoff scope: smooth tails, tail energy equality and uniqueness of the Leray–Hopf future from each solution's own trace |
| **SINGULAR-PREMISE OBSTRUCT R3** | **OPEN** | Dummy/pending | No complete named root derivation or native whole-space obstruction root is established |
| **SIGNULAR-PREMISE OBSTRUCT T3** | **`!!!!` — conditional on axiom** | Real exact conditional-theorem audits | Closed relative to the explicit `StoppedCommutatorBound` axiom for positive viscosity |

Here `!=` records a complete B-tier derivation. For WFB and QFB, `!!!!`
records closure of the exact stated theorem. WFB's finite full Fourier budget
is part of its theorem statement; all proof obligations for that implication
are closed. For T3, the qualified marker
**`!!!!` — conditional on axiom** records closure of the selected axiom-relative
target; the qualification is part of its status.
The [WFA/QFA B-tier derivations](Temp-folder/specification/FEFFERMAN_A_ELEMENTWISE_FINITE_WINDOW_B_TIER_v0_1.txt),
sections 13.1, 13.3 and 14, establish their recorded mathematical chains; their
general Lean roots remain pending.

The [WFB acceptance record](T3_NSE/B-Regularity-class/WFB/Weak_Fourierman_B_A_TIER.txt)
closes all ten contextual obligations with standard axioms and no additional
analytic certificate. Universal finiteness of the budget for every smooth
datum is a separate, stronger open question. The CI status
`CONDITIONAL_FULL_BUDGET` describes WFB's retained hypothesis; it does not
indicate an unfinished proof of WFB itself.

After the complete Material workflow succeeds on `main`, six jobs inspect that
exact source revision with `max-parallel: 6` and `fail-fast: false`. The three
dummy stages perform no Lean execution, cache restoration or theorem audit;
they record pending status and open obligations. The three real stages use
verified canonical cached objects and run fresh exact-type and axiom audits.
They do not publish partial replacement caches.

**T3 obstruction: `!!!!` — conditional on the explicit
`StoppedCommutatorBound` axiom.** The accepted theorem is

$$
\forall\nu>0,\qquad
\mathrm{StoppedCommutatorBound}(\nu)\Longrightarrow\neg\mathrm{NSE}_B(\nu).
$$

The assumption and its physical motivation are set out in the
[stopped-commutator discussion](T3_NSE/B-Heisenberg-Obstruction/StoppedCommutatorBound/README.md),
the [definition and physicists' reason trace](Material/MethbokeAddon/EhrenfestObstruction/Definitions.lean#L73)
and the [B-tier derivation](T3_NSE/B-Heisenberg-Obstruction/StoppedCommutatorBound/EHRENFEST_OBSTRUCTION_B_TIER.txt).
The [A-tier acceptance record](T3_NSE/B-Heisenberg-Obstruction/StoppedCommutatorBound/EHRENFEST_OBSTRUCTION_A_TIER.txt)
states the exact audited implication. Here “axiom” means the explicit
mathematical assumption supplied to that theorem. In Lean it remains a defined
predicate passed as a hypothesis; the theorem's axiom audit uses only
`propext`, `Classical.choice` and `Quot.sound`. Its witness has not been
constructed, and unconditional failure of NSE-B remains unresolved.

The existing complete Material verification and Lean source-count checks remain.
Validation is reported by the [theorem-goal workflow](https://github.com/randogelist/Methboke/actions/workflows/theorem-goals.yml)
for each exact source commit. Dummy-stage completion keeps the corresponding
mathematical statement pending. Earlier configurations do not validate a later
source revision.

<!-- lean-source-stats:start -->
## Lean source size

[![Lean source count](https://github.com/randogelist/Methboke/actions/workflows/lean-line-count.yml/badge.svg?branch=main)](https://github.com/randogelist/Methboke/actions/workflows/lean-line-count.yml)

**109,709 physical lines of Lean across 849 tracked .lean files** in the project tree, excluding archive/reference copies in Temp-folder/.

| Scope | Lean files | Physical lines |
|---|---:|---:|
| Non-vendored project files | 544 | 65,780 |
| Retained vendored sources ([Material/_vendor/](Material/_vendor/)) | 305 | 43,929 |
| **Project tree total** | 849 | 109,709 |
| Archive/reference copies ([Temp-folder/](Temp-folder/)) | 537 | 68,790 |
| All tracked .lean files, including archive/reference copies | 1,386 | 178,499 |

These are physical source lines, including comments, blank lines, audit consumers, and Lean build-description files. They are not an authorship or compiled-module count. Only Git-tracked filenames ending in .lean are counted; compressed archives and .lean.txt documents are not unpacked or counted.

[Lean source count CI](https://github.com/randogelist/Methboke/actions/workflows/lean-line-count.yml) recounts the files and checks this section using Python and Git only. Its JSON artifact includes the exact source commit and every counted file.

After staging source-file additions or deletions, refresh this section with:

    python3 scripts/count_lean_lines.py --write-readme
<!-- lean-source-stats:end -->

## Integration of AC resources into main

**Merged into `main`.** [PR #2](https://github.com/randogelist/Methboke/pull/2)
closed as merged on 2026-11-21 at 02:46:09 UTC. The authorized non-force
fast-forward advanced main from `4a609ea634ec4a5ff846049b9dc12b40b5f1a702`
to the verified head `e627a39e6c27cd4432ab063741fe726af8378a63`, preserving
the original integration history. The local integration target is complete.
That integration retained the then-current **Fefferman D** goal. The completed
FDSN_R3 theorem and every prior accepted result retain their exact scope; the
current six-goal declaration above supersedes the historical goal selection.

The promoted head passed [run 44856391458](https://github.com/randogelist/Methboke/actions/runs/44856391458):
**654 modules reused, zero freshly compiled, 169 fresh package audits and
2,212 named type/axiom reports plus fresh QFB**. Dependency and project caches
were both EXACT, only the approved standard axioms occurred, and recovery was
skipped. The first main run, [44857663580](https://github.com/randogelist/Methboke/actions/runs/44857663580),
also passed at the promoted commit, including final acceptance and full cache
publication. It reused **548 modules and compiled 106 additions**, with 169
fresh package audits and 2,212 named reports plus QFB; dependency cache was
EXACT and project cache PREFIX. Its donor was `572fd9ee` / run `44848985720`.
The combined cache is now published in main's scope. The subsequent documentation
head `10f73223` also completed [Material run 44859131356](https://github.com/randogelist/Methboke/actions/runs/44859131356)
with a successful conclusion. Each later main commit has its own matching CI status.

**Original combined acceptance:** `5a44e985c15a302110fd91d064431f1183e55857`,
[run 44854389941](https://github.com/randogelist/Methboke/actions/runs/44854389941).
The frozen inputs are
[`main@4a609ea`](https://github.com/randogelist/Methboke/tree/4a609ea634ec4a5ff846049b9dc12b40b5f1a702)
and
[`AC-Integration@000c1bd9`](https://github.com/randogelist/Methboke/tree/000c1bd9baded808b79a04b7f666cacabce64939).
The verified union contains **654 active modules and 183 owned modules**.
That original run reused **548 compatible cached modules** and compiled **106 modules
freshly**. All **169 package audits were fresh**, covering **2,212 named
type/axiom reports** plus the fresh standalone QFB cutout. Only `propext`,
`Classical.choice` and `Quot.sound` occur; publication and final acceptance passed.

The independent review compared complete printed types, axiom sets and
endpoint IDs for **all 1,320 main reports and all 1,402 AC reports**, with
**510 shared reports**. Every report was preserved unchanged. The compiler,
dependency and build contexts match both baselines. Dependency cache admission
is `EXACT`; project cache admission is `PREFIX`. This is matching cached
verification with fresh complete audits.

The integration uses that **frozen incoming snapshot**. Later AC-Integration
research is excluded, including `QFAHeatGenerator`, introduced at `d884a36b`
and repaired at `809aadc6`. Its two active modules, one audit package and nine
theorem targets belong to a separate follow-up. Advancing the AC branch does
not alter this integration's source boundary.

The [accepted summary](audits/integration-5a44e985-accepted/summary.json) and
[independent review](audits/integration-5a44e985-accepted/independent-review.json)
pin the original tested source `5a44e985c15a302110fd91d064431f1183e55857` and
tree `a7810ee179093a387f9740f94b544c735a886dfe`. Integrity review checked all
four ZIP digests, 825 tar members, 654 object receipts, 170 fresh audit logs
and 2,213 marked type/axiom blocks including QFB. The final gate recorded
`PRIMARY_ACCEPTED=true`.

A subsequent documentation/evidence commit is a distinct revision with its
own ordinary external head check. For its observed verification outcome, use
the **live main SHA and the latest Material run matching that exact SHA**.
The archived acceptance remains pinned to `5a44e985`; the separate promotion
record identifies the accepted PR head and observed merge into main.

The [integration record](integration/AC_INTO_MAIN/README.md),
[status](integration/AC_INTO_MAIN/INTEGRATION_STATUS.json),
[preparation report](integration/AC_INTO_MAIN/PREPARATION_REPORT.json) and
[preservation manifest](integration/AC_INTO_MAIN/PRESERVATION_MANIFEST.json)
track the exact inputs, registry union and proof preservation. The
[precommit static review](integration/AC_INTO_MAIN/reviews/PRECOMMIT_STATIC_REVIEW.json)
records the historical planned tree `a7810ee1`. Existing source, consumer,
closure and evidence identities remain source-specific. The tested index's
pending labels are launch-time metadata; the matching receipt above establishes
the completed acceptance of the original tested revision.

The incoming AC head is **A-tier accepted** at
`000c1bd9baded808b79a04b7f666cacabce64939`,
[run 44851575278](https://github.com/randogelist/Methboke/actions/runs/44851575278).
Independent review verified all **526 modules** (520 compatible reuses and six
fresh compilations), **105 fresh package audits**, **1,402 unique named
type/axiom reports**, the fresh standalone QFB cutout, permitted axioms,
publication and final acceptance. The [exact evidence](audits/material-000c1bd9-qfa-accepted/summary.json)
accepts the new 35-declaration heat-time scope. Earlier AC scopes retain their
original tested revisions. The combined revision has its separate acceptance
at `5a44e985` above.

The completed local theorem **FDSN_R3** is **A-tier accepted** at `572fd9ee`, [run 44848985720](https://github.com/randogelist/Methboke/actions/runs/44848985720). The canonical theorem `MethbokeAddon.FDSNR3.FDSN_R3` constructs the full same-witness `Family` from the original locally Schwartz `Seed`; all sixteen assented endpoint scopes have matching external evidence. The run passed **548 modules, 137 fresh package audits, 1320 named type/axiom reports and the original cutout**, followed by publication and final acceptance. [Exact acceptance evidence](audits/fdsn-r3-572fd9ee-accepted/summary.json), the [implementation ledger](R3_NSE/FDSN/IMPLEMENTATION_STATUS.json) and the [unchanged mathematical construction](R3_NSE/FDSN/FDSN_R3_B_TIER.txt) give the full scope. The theorem retains its seed premise; seed existence is not proved.

The preserved accepted local theorem is **FEFFERMAN_D_SPECTRAL_NONRIGIDITY (FDSN)** on the unit three-torus: an exact admissible preterminal seed produces a localized phase family preserving modal powers while separating translation classes and projected force histories. The [canonical proof and construction checklist](T3_NSE/D-Family-Obstruction/FDSN/FDSN_B_TIER.txt) and [implementation ledger](T3_NSE/D-Family-Obstruction/FDSN/IMPLEMENTATION_STATUS.json) track this single local target. The initial phase and bump packages passed [external CI44801643103](https://github.com/randogelist/Methboke/actions/runs/44801643103): 21 exact named declarations, standard axioms only. The canonical root and its physical presentation are now **A-tier accepted** at [run 44811785125](https://github.com/randogelist/Methboke/actions/runs/44811785125), with 317 exact audited FDSN declarations. [Accepted evidence](audits/fdsn-87ab6b4c-accepted/summary.json) and the [theorem register](T3_NSE/D-Family-Obstruction/FDSN/A_TIER_REGISTER.txt) retain the exact scope.

The preserved prescribed-site route is **Fefferman_D_Family_obstruction**. It strengthens the
existence target to every positive viscosity and every finite configuration
of distinct torus sites, with zero initial velocity, bounded preterminal cell
energy, and local velocity blowup at all prescribed sites at time one. Taking
one site gives the intended obstruction. The cumulative B-tier construction is
complete relative to the pinned compact seed; its native Lean family theorem
and literal all-order force-decay adapter remain formal obligations.

The working branch is `main`; `integration/ac-into-main` supplied the merged PR.
The [project context](GPT.txt) records the preserved mathematical scopes and
the completed integration, successful main verification and later head-check policy. The [prior goal documents](audits/goal-transition-fefferman-d/manifest.json)
retain the previous conditional Ehrenfest goal and its accepted evidence.

## Preserved periodic-family implementation

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

## Accepted direct-D endpoint and preserved family helpers

The [direct endpoint](T3_NSE/D-Family-Obstruction/UpstreamSeed/README.md)
`Methboke.FeffermanD.Fefferman_D` is **A-tier accepted** at
`66a529248d3198ed70dc5489d82868bc33a37796`,
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

## Incorporated AC mathematical resources

The following accepted resources retain the exact source revisions and scopes
established on AC-Integration. Their older full-run counts are not counts for
the new combined build. No general nonzero-data QFA, WFA, universal six-charge
budget, or new Fefferman-A theorem is inferred from their integration.
The general physical QFA target is a definition with separate proof obligations;
`QFAConditionalRoot` retains its explicit historical analytic hypotheses.
FDSN_R3 continues to use its original `Seed` and `Family` contracts unchanged.

The accepted `QFAHeatTrajectory`, `QFAHeatTimeEnergy` and
`QFAWeightedBudgetAllWindows` batch contains **35 declarations: 32 theorems
and three definitions**. It constructs actual positive-time H2 trajectory and
strong time measurability, the exact free-heat enstrophy-dissipation identity,
finite-window L2-time H2 membership and an all-window budget including zero.
The exact [heat-time construction chain](R3_NSE/QFA/DERIVATIONS/HEAT_TIME_ENERGY_CHAIN.txt)
retains the quantitative bound. Its H2 trajectory's zero extension at time
zero does not assert that arbitrary H1 input lies in H2. The preceding failures
at `d53e1fae` / run `44850402452` and `be624903` / run `44850983211` remain
historical evidence, superseded by the reviewed acceptance at `000c1bd9` /
run `44851575278`. The [matching acceptance record](audits/material-000c1bd9-qfa-accepted/summary.json)
retains the exact scope. The general QFA/WFA roots remain open.

## QFA closure progress: three new accepted scopes

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
No local Lean was executed. Fefferman D was the goal at that milestone.

The subsequent free-heat enstrophy-dissipation and finite-window L2-time
H2 construction is accepted in the 35-name batch at `000c1bd9` described above.
The pointwise smoothing bound alone is not time integrable at zero. Actual forced heat, nonlinear H1
existence, general LH existence, physical comparison, sharp spatial admission
and small-product continuation remain explicit general-data obligations.

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
record the scope and remaining edges. Retained Fefferman-D work, prior periodic
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

## Further NSE-A native work

The accepted six-target register now marks G05 complete. The remaining five
parents require native local/maximal NSE, sharp spatial admission, physical
energy/enstrophy evolution, the literal smooth class bridge and the canonical
full-budget equivalence. Reviewed B-tier derivations are retained in
[R3_NSE/A-Regularity-class/DERIVATIONS](R3_NSE/A-Regularity-class/DERIVATIONS/).
The exact failed attempts remain in the implementation history and evidence
archives; they are superseded by the matching current acceptance above.

## Repository map

`T3_NSE` and `R3_NSE` are ordinary domain folders. `Material/` retains the
shared build paths. The [relocation map](REORGANIZATION_MAP.json) preserves
the previous research-file locations.

| Path | Purpose |
|---|---|
| [GPT.txt](GPT.txt) | Six current domain goals, CI stages, retained integration and exact mathematical contracts |
| [Integration record](integration/AC_INTO_MAIN/README.md) | Frozen inputs, accepted combined scope, proof preservation and live head verification policy |
| [QFA resources](R3_NSE/QFA/README.md) | Accepted physical foundations, restart/heat/zero-datum scopes and remaining general-root obligations |
| [NSE-A resources](R3_NSE/A-Regularity-class/README.md) | Accepted pathwise six-charge resources, B-tier class characterization and remaining canonical PDE obligations |
| [Source anchors](Temp-folder/README.md) | Retained QFA/WFA source references and evidence; no acceptance by copying |
| [INDEX-WORTHY.txt](INDEX-WORTHY.txt) | Substantiated results with source-specific scope and evidence |
| [SOURCE_STATUS.json](SOURCE_STATUS.json) | Goal, implementation and accepted-evidence identities |
| [T3_NSE](T3_NSE/README.md) / [R3_NSE](R3_NSE/README.md) | Preserved periodic programs, accepted whole-space FDSN, and incorporated QFA/NSE-A resources |
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
The integration adds only its exact branch to the existing push trigger;
the established verification gates and cache policy remain in force.
The separate direct-D 4.34.0-rc2 project retains its own lock and compiled
objects. The 35 exact QFA vendor additions retain separate provenance;
the two failed/inactive upstream modules stay outside active imports.


## Historical FDSN verification attempts

The following repairs are superseded by the current full acceptance recorded below.

The second FDSN run stopped at a finite-sum congruence elaboration error. Its statement-preserving repair was prepared and subsequently accepted; [failure evidence](audits/fdsn-1cb76bc0-failed/summary.json) is retained.

The next full-chain candidate includes the repaired localized spacetime wrapper and the actual active-triad, residual-force, smallness and separation arguments. [The preceding failed-run evidence](audits/fdsn-dbbfe1e9-failed/summary.json) is retained; it gives no new acceptance.

FDSN verification repair after run44805483799: Normalize pointwise functions and native vector/slice coercions, replace the reserved lambda token with an alpha-equivalent identifier, and repair one malformed audit consumer; add a separate physical Leray interpretation adapter. [Failure record](audits/fdsn-25c5a4e3-failed/summary.json).

FDSN verification repair after run44806525675: Resolve the finite-norm estimate elaboration, explicit zero-velocity germs, inequality addition orientation and pointwise coefficient coercions; include the same-witness physical presentation corollary. [Failure record](audits/fdsn-bfddc915-failed/summary.json).

FDSN verification repair after run44807597711: Make residual smoothness subterms explicit with a scoped elaboration allowance, and normalize subtraction in the physical Leray coefficient identity. All theorem contracts are unchanged. [Failure record](audits/fdsn-38dd6ec5-failed/summary.json).

FDSN verification repair after run44808681563: Specify the exact inner and outer maps in both joint residual derivative compositions; theorem statements and audit consumers unchanged. [Failure record](audits/fdsn-6f02f8b7-failed/summary.json).

FDSN verification repair after run44809750811: Normalize the actual correction value in the initial-time vanishing-germ equality before rewriting; one proof line changed, all theorem contracts preserved. [Failure record](audits/fdsn-fe0ba0f3-failed/summary.json).

FDSN verification repair after run44810618725: Give all compact force-correction proof components explicit types and scope a larger elaboration budget to that single declaration; exact theorem and consumer contract unchanged. [Failure record](audits/fdsn-a75f3f0c-failed/summary.json).

## Accepted periodic FDSN root

The exact conditional theorem on the unit three-torus passed at `87ab6b4cfc4a81a1fb6c8e37bb6d5caf3972b1ef`. The same family satisfies all five canonical clauses; the physical presentation gives a literal nonzero Leray-projected force difference. The [construction and acceptance note](T3_NSE/D-Family-Obstruction/FDSN/FDSN_CONSTRUCTION_AND_ACCEPTANCE.txt) records the proof route. Historical repair entries above are superseded by this acceptance; their evidence remains preserved.


## Historical R3 construction and verification attempts

The preparation and failure notes in this section describe their original
source revisions. Their pending labels are superseded by the accepted
`572fd9ee` root recorded above and below; all failure receipts remain retained.

The first R3 verification stopped at a smoothness-order coercion. Its
[retained failure evidence](audits/fdsn-r3-5914a69a-failed/summary.json) and
statement-preserving repair are tracked separately from accepted results.

The R3 second stage introduces six packages with129declarations for actual
Fourier calculus, Schwartz slice admission, nonzero frequency patches, helical
projectors, odd cutoffs and translation rigidity. These candidates await
matching external verification. B-tier v1.1 adds a direct force-separation
proof at a signed time-phase zero crossing, preserving the exact theorem.

Stage2 verification found proof elaboration errors in Fourier, helical and
cutoff sources. [Failure evidence](audits/fdsn-r3-d2ec178-failed/SUMMARY.txt)
is retained; statement-preserving repairs are prepared for the next external run.

The stage2 retry narrowed the remaining errors to two proof details; the
cutoff source and wrapper compiled. [Retained evidence](audits/fdsn-r3-db246dbe-failed/SUMMARY.txt)
records the failed run. The next repair changes no theorem statement.

The next stage2 run compiled the Fourier, helical, cutoff and translation
sources. A proof-only nonzero-patch repair follows its
[retained diagnostics](audits/fdsn-r3-a568ec75-failed/SUMMARY.txt).
Acceptance still requires the complete fresh type and axiom audits.

## Historical full R3 construction preparation

The prepared construction now includes actual joint Fourier differentiation
and inverse reconstruction, a globally Schwartz velocity correction and its
native nonlinear residual, force admission, common compact temporal support,
all weighted finite-order parameter estimates, and the canonical root.
One family supplies every clause. With the explicit fixed-frame bridge and
time-integrated dissipation consequence, the registry contains137packages
and1320named declarations;421stage2/stage3 declarations await acceptance.

The latest completed run reached the spatial-slice affine-law proof. Its
[retained diagnostics](audits/fdsn-r3-0f68d4a1-failed/SUMMARY.txt) are addressed
by a binder-order correction with unchanged theorem statements. Full external
compilation and fresh exact-type/axiom reports remain required.

The first full R3 run compiled every second-stage source. Six new analytic
modules required proof/coercion repairs, now prepared with unchanged
mathematical scope. [The complete diagnostics](audits/fdsn-r3-54f6c70b-failed/SUMMARY.txt)
are retained; no new A-tier acceptance follows from this failed run.

Run44837788551 cleared four analytic source failures. Three remaining source errors have prepared coercion and literal zero-integral repairs; fresh audits remain pending.
[Retained external diagnostics](audits/fdsn-r3-f44d4e1f-failed/SUMMARY.txt) accompany the
prepared statement-preserving repair. Full fresh audits remain required.

Run 44838626146 compiled the spectral generator and narrowed the next reported failures to three source proofs. Exact curry-isometry, slice-jet conversion and scalar-divergence repairs are prepared; full fresh audits remain pending.
[Retained external diagnostics](audits/fdsn-r3-afa16302-failed/SUMMARY.txt) accompany the
prepared statement-preserving repair. Full fresh audits remain required.

Run 44839269539 compiled the slice-jet and physical Leray helper layers and reached the joint residual source. Two reported proof failures have exact normalization repairs prepared; full fresh audits remain pending.
[Retained external diagnostics](audits/fdsn-r3-a24c4179-failed/SUMMARY.txt) accompany the
prepared statement-preserving repair. Full fresh audits remain required.

Run 44840058960 isolated two remaining reported instance-inference errors. Their exact typed-map repairs are prepared, alongside four explicit fixed-frame and integrated-dissipation scope-completion declarations. The complete candidate now requires 137 packages and 1320 fresh named reports.
[Retained external diagnostics](audits/fdsn-r3-4911da18-failed/SUMMARY.txt) accompany the
prepared statement-preserving repair. Full fresh audits remain required.


Earlier R3 repair: [run44840893717](https://github.com/randogelist/Methboke/actions/runs/44840893717)
compiled the joint residual and fixed-frame layers, then stopped in the
parameter-integral and zero-parameter residual proofs. The statement-preserving
repairs use the actual continuous-linear curry equivalence and explicit
zero-function normalization. [Failure evidence](audits/fdsn-r3-8e75aa4f-failed/SUMMARY.txt)
records 532 passing modules, 2 failures and 14 blocked dependencies. Fresh
named audits were not reached; the R3 root remains pending external acceptance.


Earlier R3 verification: [run44842165398](https://github.com/randogelist/Methboke/actions/runs/44842165398)
compiled the residual-admission layer and left one source failure in the
parameter-integral proof. The actual curry operation is now explicitly bundled
with the intended normed instances. The original statements and audit consumers
are unchanged; all fresh audits and full root acceptance remain pending.
Failure evidence: [d5acd494](audits/fdsn-r3-d5acd494-failed/SUMMARY.txt).

## Previous R3 verification

[Run 44842918759](https://github.com/randogelist/Methboke/actions/runs/44842918759)
at `8b49f5c0` failed in `ParametricFourier` while elaborating the bundled
continuous linear curry map: **534 modules passed, one failed and thirteen
were blocked**. No fresh endpoint audit ran. The prepared replacement constructs
the continuous linear map directly and supplies explicit integral-commutation
types. The original theorem statements, Seed, Family and independent consumers
remain unchanged.

[The complete failure evidence](audits/fdsn-r3-8b49f5c0-failed/SUMMARY.txt)
is retained. Matching external cached compilation and all required fresh exact-type
and theorem-level axiom reports remain pending for the 137-package,
1320-declaration candidate. No new A-tier acceptance is claimed.

## Previous R3 verification

[Run 44844086846](https://github.com/randogelist/Methboke/actions/runs/44844086846)
at `f07a4c6a` compiled `ParametricFourier` and its endpoint wrapper. It then
reached two analytic source failures in `CompactFrequencyInverse` and
`ForwardFourierSmooth`: **536 modules passed, two failed and ten were blocked**.
No fresh endpoint audit ran.

The next candidate contains source-only elaboration repairs: explicit Dirac
Fourier-integral evaluation, typed multilinear coefficients and operator-norm
bounds, and explicit affine-slice, coercion, composition and Schwartz-map
arguments. The original theorem statements, Seed, Family and independent
consumers remain unchanged. [The complete failure evidence](audits/fdsn-r3-f07a4c6a-failed/SUMMARY.txt)
is retained. Matching external cached compilation and all required fresh exact-type
and theorem-level axiom reports remain pending; no new A-tier acceptance is claimed.

## Previous R3 verification

[Run44844863588](https://github.com/randogelist/Methboke/actions/runs/44844863588)
at `8ff47f2e` cleared the previous analytic diagnostics; affine-slice normalization,
a missing index binder and two integrability-type metavariables remain.
**536 modules passed, two failed, ten were blocked; no fresh audit ran.**
The next candidate applies minimal source-only repairs with unchanged theorem
statements. [Exact failure evidence](audits/fdsn-r3-8ff47f2e-failed/SUMMARY.txt)
is retained; full matching external acceptance remains pending.

## Previous R3 verification

[Run44845509310](https://github.com/randogelist/Methboke/actions/runs/44845509310)
at `f5fb09b7` leaves two proof-normalization errors: a natural-zero coercion
in the compact Fourier bound and additive orientation in the forward Fourier bound.
**536 modules passed, two failed, ten were blocked; no fresh audit ran.**
Minimal source repairs preserve the theorem statements.
[Exact evidence](audits/fdsn-r3-f5fb09b7-failed/SUMMARY.txt)
is retained; full matching external acceptance remains pending.

## Previous R3 verification

[Run44846133642](https://github.com/randogelist/Methboke/actions/runs/44846133642)
at `44725d62` compiled both compact and forward Fourier layers and their wrappers.
It reached `JointPacket` and `CrossingDerivative` elaboration failures:
**540 modules passed, two failed, six were blocked; no fresh audit ran.**
Explicit bump/Fourier composition and pointwise derivative repairs preserve
the original statements. [Exact evidence](audits/fdsn-r3-44725d62-failed/SUMMARY.txt)
is retained; full matching external acceptance remains pending.

## Previous R3 verification

[Run44846785644](https://github.com/randogelist/Methboke/actions/runs/44846785644)
at `5423da48` compiled **all548 modules, including the canonical Seed-to-Family
root**. It recorded52 fresh passing endpoint audits covering537 declarations,
then failed on an unavailable namespace in `FDSNR3CrossingTimePhase/Audit.lean`.
The sole repair removes an unused namespace opening; all10 independent consumers
and10 named type/axiom targets are byte-preserved. No theorem source changes.
[Exact partial evidence](audits/fdsn-r3-5423da48-failed/SUMMARY.txt)
is retained. Complete fresh audits, the cutout and final acceptance/publication
remain pending; no new root or endpoint A-tier acceptance is claimed.

## Previous R3 verification

[Run 44847910880](https://github.com/randogelist/Methboke/actions/runs/44847910880)
at `7dd6dba6` compiled **all 548 modules, including the canonical Seed-to-Family
root**, and recorded **55 fresh passing package audits covering 571 declarations**.
The corrected CrossingTimePhase audit passes. The run then stopped at an
independent Fourier consumer whose missing intermediate Schwartz-map type
selected an unavailable Fourier-transform instance. The next candidate adds
that explicit type to the same identity; all 33 consumers and 33 named targets
are retained, with no theorem source changes.
[Exact partial evidence](audits/fdsn-r3-7dd6dba6-failed/SUMMARY.txt) is retained.
Complete fresh audits, the original cutout and final acceptance/publication
remain pending; no new root or endpoint A-tier acceptance is claimed.

## Accepted whole-space FDSN_R3 root

The complete conditional root and all sixteen user-assented endpoint scopes are
**A-tier accepted** at `572fd9ee69a6b641f435cbfb2ef74e034809c583`, [run 44848985720](https://github.com/randogelist/Methboke/actions/runs/44848985720). The reviewed run passed
all **548 modules, 137 fresh package audits and 1320 exact named reports**, plus
the original cutout, with only `propext`, `Classical.choice` and `Quot.sound`.
The root is `Seed ν T u p F → Family ν T u p F` with the original contracts.
There are 493 R3 declarations across 26 R3 packages; 421 declarations are newly
accepted beyond the retained 72-declaration foundations. Prior T3 scopes remain intact.

[Complete evidence](audits/fdsn-r3-572fd9ee-accepted/summary.json) includes the original artifact, exact source
map, fresh logs, independent review and successful publication/final acceptance.
The accepted archive preserves the tested endpoint manifests, dependency closures, owned-source provenance and audit/policy inputs byte-for-byte. The integration unions the current source and endpoint registries while preserving every original entry and proof/consumer byte. Their launch-time PENDING_EXTERNAL_CI/false labels remain historical preparation metadata; this matching source-specific acceptance record and the synchronized implementation ledger establish the current accepted status. A later documentation-only commit is not the tested proof commit.

Earlier pending descriptions are dated preparation history, superseded by this
acceptance. Seed existence and the separate prescribed-site family remain outside
this accepted conditional R3 result. No local Lean execution was used.
