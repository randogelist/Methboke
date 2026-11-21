# AC-Integration: endpoint dependency map

## Scope and evidence status

This is a staging and integration map for the `AC-Integration` branch. The macro goal remains **Fefferman_D**. Adding the QFA/WFA reference material does not change that goal or replace the existing Methboke proofs, toolchain pins, or external evidence.

The 15 obligations below are **proposed formalization obligations**, not user-assented formalization targets or newly accepted results. The cumulative mathematical specification is [the cumulative B-tier specification](specification/FEFFERMAN_A_ELEMENTWISE_FINITE_WINDOW_B_TIER_v0_1.txt). The October archives are preserved source material; their historical names and status strings do not establish A-tier evidence for QFA/WFA.

No Lean, Lake, Rocq, kernel audit, or included project runner was executed during staging. No mathematical derivation or source proof was changed.

## Current ten-step construction checklist

The latest request names QFA/QFB. The [ten-step checklist](QFA_QFB_10_STEP_CHECKLIST.md)
constructs QFA alongside accepted QFB and preserves its exact cutoff and
representative conventions. The fifteen-obligation map below remains the
broader QFA/WFA reference; its Fourier-budget, initial-window and literal
global-A tasks are separate follow-ons to the QFA tail construction.

## Archive layout and direct dependencies

| Component | Staged archive | Unpacked root |
|---|---|---|
| Core definitions and historical MasterAC program | `archives/FEF_NSE_MASTERAC_TWO_LAYER_LEAN_v0_11_0.zip` | `unpacked/FEF_NSE_MASTERAC_TWO_LAYER_LEAN_v0_11_0/` |
| Concrete-real closure endpoints | `archives/FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0.zip` | `unpacked/FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0/` |

Each ZIP has one leading directory equal to its ZIP stem. That prefix was removed once when extracting into the already named `unpacked/<ZIP stem>/` directory. Every member-to-path mapping and file SHA-256 is recorded in [provenance/october.json](provenance/october.json); original ZIP bytes and extracted member bytes were verified.

`ConcreteABCDUnifiedClosure.lean` imports only `Mathlib`, `Fefferman.Analysis`, and `Fefferman.Statements`. `Statements` imports `Analysis`, which imports `Init`. The two project imports come from v0.11.0. The historical v0.25.0 runner additionally extracts the complete v0.11.0 ZIP and invokes its complete build, so v0.11.0 is an actual packaging dependency even though the concrete closure module does not import the MasterAC or physics graph.

The v0.25.0 Lean file includes all 2,940 lines of v0.24.0's `ConcreteWholeSpaceAAClosure.lean` unchanged, followed by 162 lines of unified endpoint packaging. It does not import v0.24.0. A separate v0.24.0 archive is therefore unnecessary for this staging scope, and both duplicate closure modules should not be used as independent definitions in one integration.

Historical runners target native Windows Lean 4.33.0. The v0.25.0 runner discovers a pre-existing Mathlib cache and does not supply an exact Mathlib commit pin. These historical environment assumptions must be reconciled with Methboke's existing pinned environment; they are not authority to replace its toolchain or lockfiles.

## What the October material supplies

The v0.11.0 core supplies the abstract `Analysis` signature, official-clause predicates, admissible data, and `globalSolution`/`hasGlobalSolution`/`A`–`D` definitions. Its continuation and research-route records are not concrete Leray–Hopf or maximal-H1 existence theorems.

The v0.25.0 module supplies a concrete `realAnalysis` interpretation using real derivatives, smoothness, integrability, and energy integrals, together with substantive force-periodization and derivative-translation lemmas. Its whole-space A closure is an endpoint equivalence: `WholeSpaceAPhysicalPort.globalZeroForce` is the global-existence proposition itself, and `WHOLESPACE_ZERO_FORCE_GLOBAL_REGULARITY_IFF_A` identifies that proposition with `A realAnalysis`.

Consequently the closure layer is a useful target interface. It does not itself discharge the actual whole-space local/weak solution theory, Sobolev estimates, Fourier identity, restart results, or finite-window continuation estimates needed below. Those must become proved imports or proved integration results. Merely adding them as fields would retain them as assumptions.

The optional Rocq package `awpi_nse_r3_h12_bkqr_gp_v0_53_3.zip` is not included: its finite spectral/BKQR/source-budget route is not an import dependency of these Lean modules and is not required by the current Sobolev/energy QFA–WFA argument.

## Fifteen proposed QFA/WFA obligations

| ID | Obligation | Existing mathematical specification / role |
|---|---|---|
| O01 | Concrete R3 solution semantics | Match whole-space fields, physical norms, admissible data, time-boundary derivatives, and official solution predicates to the concrete closure interface. |
| O02 | Whole-space Sobolev, interpolation, Hessian estimates, and S6 | E01–E02: fix the real whole-space constant and its vector/tensor use; prove the estimates used by the nonlinear bounds. |
| O03 | Continuous Fourier/Plancherel normalization | E13: prove the full continuous charge identity `Q_A = ||grad U||_2^2/(4 pi^2)` for the specified Fourier convention. |
| O04 | Canonical local H1 strong theory, maximality, and pressure | A0–A1: actual existence, uniqueness, continuation alternative, and Schwartz-data smoothness including initial pressure. |
| O05 | Global Leray–Hopf existence and admissible restarts | A2: all solenoidal L2 data; weak L2 continuity, strong energy inequality from good starting times, H1 traces, and right strong L2 traces. |
| O06 | Weak–strong uniqueness | A3: identify solutions from the same exact restart trace within the Leray–Hopf energy class. |
| O07 | Actual energy/enstrophy and nonlinear inequalities | E02, E04–E06: derive the identities and bounds for the actual solutions, with the stated constants. |
| O08 | Initial closed smooth window and charge | E03–E04, E16: establish strict existence beyond `T_loc`, the closed-window conclusion, and its charge bound; handle zero data separately. |
| O09 | Small-product global restart | E05: an actual divergencefree H1 datum with sufficiently small energy–enstrophy product has a global strong continuation. |
| O10 | Weighted energy integral | E06: derive the integrated `E Y` bound from the strong energy inequality. |
| O11 | Positive-measure good-time selection | E07: find a small-product admissible restart strictly before the safe datum-dependent cutoff; include the zero-data branch. |
| O12 | QFA tail, energy equality, and future uniqueness | E12: every specified Leray–Hopf solution has the stated smooth tail, including the safe cutoff, and a unique future from each of its own tail traces. |
| O13 | Full extended/improper budget and strict cutoff crossing | E08–E09: preserve possible infinite budget values and prove `T_max > tau_A`, including exclusion of equality. A totalized real integral must not conceal divergence. |
| O14 | WFA finite budget implies globality, with datumwise converse | E10, E14: continue the original maximal strong trajectory globally under the full-budget premise, and prove the converse for a global trajectory. |
| O15 | Literal Fefferman-A solution-class bridge | A4, E10: connect the canonical strong result and the literal smooth finite-energy class on closed finite slabs, with normalized pressure or a smooth time gauge. |

O01–O07 supply the analytic foundation. O08 is the initial certificate. O09–O11, together with O05–O06, yield O12. O03, O04, O07 and O13 support the finite-window argument; O09 and O11 complete O14. O15 connects that result to the official A predicate.

## Retained logical boundary

QFA is the unconditional eventual-regularity statement. WFA is the conditional theorem that a finite full-spectrum squared-charge budget implies global classical continuation. Future uniqueness in QFA is from the trace of each particular weak solution; it does not assert identical traces for all weak solutions from the original datum.

Universal finiteness of the WFA budget remains a separate open obligation. With the solution-class bridge, that universal budget would imply the whole-space global endpoint and hence `A realAnalysis`; WFA alone does not fill `WholeSpaceAPhysicalPort`. None of these staging steps supplies that universal estimate or changes the Fefferman_D macro goal.

Any eventual A-tier designation must attach to the exact resulting source and its matching authorized external compiler and theorem-level dependency evidence. Existing archived evidence is retained as historical evidence and does not automatically verify the proposed integration.

## Pinned periodic sources and evidence

The complete tested project snapshot is in
[`unpacked/METHBOKE_QFB_WFB_SOURCE_fdb515d8/`](unpacked/METHBOKE_QFB_WFB_SOURCE_fdb515d8/).
It includes the QFB, WFB, SingularClosure and package dependencies at the same
immutable commit. Its historical root documents are reference material; the
current branch context is the repository's root GPT.txt.

| Reuse family | Source within the pinned snapshot | Role in this integration |
|---|---|---|
| QFB semantics and tail | `Material/_vendor/QuasiFeffermanB/` | Reference for weak-solution contracts, restart, tail energy and future uniqueness |
| Physical analytic foundation | `Material/_vendor/SingularClosure/` | Source for inspecting exact PDE/function-space assumptions and reusable estimates |
| WFB local and maximal trajectory | `Material/MethbokeAddon/WeakFouriermanB/` | Reference for local existence, maximality, continuation, finite budget and same-path gluing |
| Exact packaged endpoints | `Material/QFB*/` and `Material/WFB*/` | Audit declarations, source imports and existing endpoint manifests |
| Dependency identity | `Material/lean-toolchain`, `Material/lake-manifest.json` | The tested compiler and package lock; preserve these identities |

The evidence is unpacked in [`evidence/material-fdb515d8/`](evidence/material-fdb515d8/).
Its `current.json` report and audit logs remain historical periodic evidence.
Domain-neutral scalar and measure lemmas are reuse candidates. Periodic
Poincare estimates, discrete Fourier sums and periodic solution semantics
need their actual whole-space counterparts for QFA/WFA.
