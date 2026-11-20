# QFA/QFB: Lean anchor register

Date: 2026-11-20. Branch: **AC-Integration**.

**The ten checklist rows now have concrete source anchors.** The strongest
new recovery is Methlib's `QFA` branch at
`53b2318c2b586137b6db74c4d3a41bb0b964b2d8`: it already contains the exact
weighted-energy proof, full-volume L² representation, strong-trace and
relative-energy helpers, corrected compact-Schwartz density, and conditional
tail assembly. These are reusable results with specific hypotheses. The
complete physical R³ QFA theorem remains open in the inspected sources.

The parent [ten-step checklist](../QFA_QFB_10_STEP_CHECKLIST.md) retains its
construction boxes. Filling an anchor slot does not discharge an analytic
premise or create a new A-tier result. This work is nonexecuting source
inspection and preparation; no Lean, Lake, local kernel audit or runner was
executed, and no new external verification was dispatched.

## Source identities and evidence

| Source | Fixed identity | Evidence used here |
|---|---|---|
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` | Complete pinned source retrieved; selected declarations inspected by exact name/type. No new adapter audit. |
| Native Methboke / periodic QFB | `fdb515d8bde35ec8021bbc26f360aca8dfa2855c` | Retained external run `44566880192`, artifact `14553501775`; each selected theorem retains its original periodic or generic scope. |
| Methlib vendor reference | `96033dd69c994bec337a87369a6c27256e724980` | Static source and historical QFB provenance; does not substitute for the separate QFA branch. |
| **Methlib QFA** | **`53b2318c2b586137b6db74c4d3a41bb0b964b2d8`** | All 301 QFA-directory files match pinned Git blobs. All 34 endpoint manifest files match the tested `9b6ca616` sources; the retained report contains full types and standard-axiom reports for 108 declarations. |
| Corrected QFA bridge/density/root | Source unchanged from tested `d792554e`, `f7ffe9e2`, `41188cef` | Matching native Windows runs `43550563998`, `43552566360`, `43554315545` are successful. Source/configuration comparisons cover 35, 41 and 48 files including local package dependencies. The root is a conditional implication. |
| Upstream R³ comparison | `openai/NavierStokesAndEuler@f9e8bc5b38b6e212696e8a30e3e91517af887bbd` | Static inspection only; separate Lean `4.34.0-rc2` environment. No native `4.33.0` compatibility or new acceptance is claimed. |

The [source review](SOURCE_REVIEW.json) records hashes, exact source matches,
observed remote run identities and the limits of the evidence. Complete
historical QFA sources and CI records are preserved in
[METHLIB_QFA_ENDPOINTS_53b2318c.zip](../archives/METHLIB_QFA_ENDPOINTS_53b2318c.zip).
This ZIP is a newly made export of the pinned directory, not an original
historical archive name. Its 62 selected endpoint/source/configuration files
are [unpacked](../unpacked/METHLIB_QFA_ENDPOINTS_53b2318c/).
The corrected-root evidence retained here is summary-level; it is distinguished
from the 108-declaration endpoint report with full printed types and axioms.

The old QFA development uses `‖a‖⁴/(16π²ν⁵)`. The present checklist uses
`8‖a‖⁴/(27π⁴ν⁵)`. Helpers independent of the old numerical cutoff transfer
under their stated hypotheses; the old numeric selector and old root do not
certify the new cutoff.

## Ten-step coverage

In this table, **direct** means that the existing theorem fits the indicated
subproblem under its stated hypotheses. **Adapt** means a concrete bridge or
specialization remains. **Model** means that the existing result has a
different domain or solution class. **Conditional** means an analytic input
is still a theorem parameter or record field.

| Step | Suitable existing anchors | Native work still needed | Assessment |
|---|---|---|---|
| **1. Concrete R³ contract** | Mathlib `Lp`, `MemLp.toLp`; Methlib `RealSpatialL2`, `EnergyProfile`, `RealTestWeakDirectionalDerivative`, `complexifyL2LI`; native spatial NSE operators; QFB `RootContract` | Define the actual all-L²σ whole-space LH predicate, weak momentum equation, pressure/tail semantics and root quantifiers. Prove the adapters from that predicate to the existing energy/derivative profiles. | Concrete foundations; physical contract open. |
| **2. Spatial estimates** | Mathlib `eLpNorm_le_eLpNorm_fderiv_of_eq_inner`, general-measure Hölder, `Lp.norm_fourier_eq`; Methlib compact-Schwartz density and `gradient_fourier_ae` / `laplacian_fourier_ae` | Extend compact C¹ Sobolev to the actual H¹ class; reconcile operator and Frobenius norms; prove the required sharp S₆ and full physical H² Hessian–Laplacian identity. | Direct foundations plus analytic adapters. |
| **3. Local H¹ theory and continuation** | Native `uniform_H1_local_initial_classical_front_exists`; periodic `EXACT_H1_ADMISSION_UNCONDITIONAL`; upstream `StrongSolutionOnIcc` | Construct R³ solutions for arbitrary H¹σ restart data, bounded-H¹ continuation, smoothing and pressure. The native local theorem begins with smooth periodic data; the upstream H³ record describes supplied solutions. | Models/contracts; actual R³ theorem open. |
| **4. Global LH and restart** | Periodic `Q01_LERAY_HOPF_EXISTENCE`, `LH_RESTART_AE_Ioo`; Methlib `strong_right_trace_of_energy_start`, `restartData_of_energyStart` | Prove all-L²σ R³ LH existence and the full-measure admissible-start properties; translate the weak momentum equation and prove membership in the actual shifted LH class. | Direct trace/energy helpers; PDE existence and membership open. |
| **5. Weak–strong comparison** | Methlib `eq_on_Icc_of_ae_relative_energy`, `ComparisonData.eq_on_Icc`; native periodic Serrin comparison | Derive the relative-energy inequality and its coefficient/product integrability from actual R³ LH and strong solutions with the same trace. Existing upstream H³ comparison requires two strong solutions. | Direct comparison mechanism; physical premises open. |
| **6. Small-product global continuation** | Methlib `ScalarProfile.enstrophy_absorption` and conditional analytic assembly; native small-data caloric admission as a periodic model | Prove actual R³ energy/enstrophy balances, the specified S₆ nonlinear estimate, the strict temporal bootstrap and the continuation instance. Pointwise scalar absorption is insufficient for evolution. | Scalar helper/conditional model; R³ global restart open. |
| **7. Weighted energy** | **`QFA.Energy.product_budget`**, `product_budget_Ioo`; **`QFA.Representation.EnergyProfile.energy_product_budget_Ioo`** | Construct the already specified `EnergyProfile` from the concrete LH predicate. | **Exact scalar proof and full-volume L² profile wrapper recovered.** |
| **8. Good time and new cutoff** | **`QFA.Endpoints.GoodTime.exists_good_time_of_integral_lt`**; Mathlib `mul_meas_ge_le_integral_of_nonneg`; existing Hilbert trace/restart helpers | Specialize to current θ, τA; prove the half-measure bound; intersect the physical restart set; handle zero data. | Direct generic selector; current constants/physical wrapper open. |
| **9. Smooth tail and energy equality** | QFB `HAS_SMOOTH_TAIL_OF_POSITIVE_FLOW`, `physicalH1_gradient_eq_smooth`, `LH_TAIL_ENERGY_OF_POSITIVE_FLOW`; generic integral/time-shift identities | Produce the actual R³ reference with pressure, identify it with the selected LH path at every time, transfer weak gradients a.e. in time, and prove the closed-tail energy identity. | Periodic proof model; R³ PDE tail open. |
| **10. Unique future and root** | Methlib `restricted_restart_class_eq_singleton`, `selectedTail_restricted_singleton`; periodic `LH_RESTART_OF_TAIL_ENERGY`, `LH_UNIQUE_FUTURE_OF_SMOOTH_FLOW`, `QUASI_FEFFERMAN_B_COMPOSED` | Prove future LH membership and fresh comparison from each exact tail trace, then assemble the physical QFA root with current cutoff and explicit energy equality. | Direct set/equality assembly; physical realization open. |

Exact declarations, full source signatures, locations, hashes and individual
evidence qualifications are in the [spatial report](reports/spatial.md),
[solution-theory report](reports/solution_theory.md), and
[scalar/tail report](reports/tail_scalar.md), with corresponding JSON files.

## 1–2. Concrete continuum foundations

The recovered Methlib representation uses
`Lp (EuclideanSpace ℝ (Fin 3)) 2 volume`, with full-volume Lebesgue measure.
`complexifyVectorLI` and `complexifyL2LI` are actual linear isometries.
`complexifyL2_gradientEnergy` preserves the sum of the three directional
L² norm squares. These avoid introducing an unexplained coordinate factor.
`RealTestWeakDirectionalDerivative` quantifies over all real smooth compactly
supported scalar tests. See
[Complexification.lean](../unpacked/METHLIB_QFA_ENDPOINTS_53b2318c/LeanEndpoints/QFA/Endpoints/Representation/Complexification.lean).

For Sobolev, the exact Mathlib theorem is
[`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean).
Its inputs include `ContDiff ℝ 1 u`, compact support, finite-dimensional
domain with Haar measure, Hilbert codomain, and the exponent relation.
Specializing to dimension 3 and exponents 2 and 6 supplies a genuine
whole-space estimate for that class. Its constant
`eLpNormLESNormFDerivOfEqInnerConst` is not the sharp constant in our target.

For the Fourier/weak-derivative route, use the corrected bridge:

- [LC005 Density.lean](../unpacked/METHLIB_QFA_ENDPOINTS_53b2318c/LC005Density/QFALC005/Density.lean): `SchwartzMap.qfa_dense_hasCompactSupport` and `schwartzDerivativeWitnesses_of_compactSchwartz_unconditional` discharge compact-Schwartz density and the corrected test extension.
- [LC001 DistributionMultipliers.lean](../unpacked/METHLIB_QFA_ENDPOINTS_53b2318c/LC001SpectralReduction/QFALC001Reduction/DistributionMultipliers.lean): `gradient_fourier_ae` and `laplacian_fourier_ae` supply exact a.e. multipliers for actual L² representatives. Their source was inspected; no matching retained LC001 package audit was found in this directory.
- [NativeFromAENorms.lean](../unpacked/METHLIB_QFA_ENDPOINTS_53b2318c/LC001SpectralReduction/QFALC001Reduction/NativeFromAENorms.lean): `nativeSpectralRealization_of_fourierNormAE` assembles a spectral record **from supplied summed norm identities**. Those inputs still need to be discharged.
- [Mathlib LpSpace.lean](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Fourier/LpSpace.lean): `MeasureTheory.Lp.fourierTransformₗᵢ` and `norm_fourier_eq` provide full continuous L² Plancherel.

Schwartz density is not automatically density in the physical weak-gradient
H¹/H² norm. That extension, tensor norm bookkeeping and the final Hessian
identity must refer to the same spaces used by the solution theory.

## 3–6. Where the analytic construction still starts

The native periodic proofs are valuable construction models. Their domain
and initial-data restrictions must remain visible: the local front theorem
uses `SmoothSigmaZero`, while `EXACT_H1_ADMISSION_UNCONDITIONAL` is a periodic
small-data theorem. Neither supplies arbitrary whole-space H¹ local theory.
The upstream [H3StrongSolution](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/H3StrongSolution.lean)
and [H3WeakStrong](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/H3WeakStrong.lean)
provide real R³ strong-solution structures and comparison results, with
two strong-solution inputs and additional comparison bounds.

Methlib's [RestartData](../unpacked/METHLIB_QFA_ENDPOINTS_53b2318c/LeanEndpoints/QFA/Assembly/Restart.lean)
constructs translated energy data, weak pairing continuity and strong traces.
It does not contain the translated weak momentum equation or LH membership.
Likewise, [relative-energy comparison](../unpacked/METHLIB_QFA_ENDPOINTS_53b2318c/LeanEndpoints/QFA/Assembly/Comparison.lean)
proves equality at every time from the stated relative-energy assumptions.
The energy inequality itself must be derived for the physical solution pair.

The [corrected analytic assembly](../unpacked/METHLIB_QFA_ENDPOINTS_53b2318c/CorrectedPhysicalRoot/QFACorrectedRoot/Analytic.lean)
still takes the spectral and Agmon endpoints and an actual reference-construction
backend. `ScalarProfile.enstrophy_absorption` is pointwise algebra applied to
a supplied derivative value. A global evolution, an invariant over time and
a continuation theorem are additional work.

## 7. The exact weighted-energy anchor is already available

Set `M = ‖a‖₂`, `D = Y` and retain `E = ‖u‖₂²`. The recovered
[`QFA.Energy.product_budget`](../unpacked/METHLIB_QFA_ENDPOINTS_53b2318c/LeanEndpoints/QFA/Endpoints/Energy/ProductBudget.lean)
assumes `T ≥ 0`, `ν > 0`, interval integrability of D, a.e. measurability of E,
nonnegativity of E and D, and

\[
 E(t)\le A(t):=M^2-2\nu\int_0^tD(r)\,dr\quad\text{a.e.}
\]

It **proves** product integrability and

\[
 \int_0^T E(t)D(t)\,dt
 \le \frac{M^4-A(T)^2}{4\nu}
 \le \frac{M^4}{4\nu}.
\]

`envelope_product_integral` proves the exact square identity internally from
absolute continuity. The proof never differentiates the weak energy E.
The full-volume L² specialization is already
[`QFA.Representation.EnergyProfile.energy_product_budget_Ioo`](../unpacked/METHLIB_QFA_ENDPOINTS_53b2318c/LeanEndpoints/QFA/Endpoints/Representation/EnergyProfile.lean).
It consumes an energy profile whose fields must be supplied by the concrete
LH theorem. Thus the new work here is that physical adapter, not a replacement
proof of the scalar bound.

## 8. Reuse the generic selector with the new constants

The direct anchor is
[`QFA.Endpoints.GoodTime.exists_good_time_of_integral_lt`](../unpacked/METHLIB_QFA_ENDPOINTS_53b2318c/LeanEndpoints/QFA/Endpoints/GoodTime/Basic.lean).
It retains an arbitrary a.e. `Good` predicate. For nonzero data the current
specification asks for the specialization

\[
 f=EY,\qquad c=\theta=\nu^4/S_6^6,\qquad
 T=\tau_A=S_6^6E_0^2/(2\nu^5).
\]

The existing weighted bound gives half the threshold integral:
`E0²/(4ν) = θτA/2 < θτA`. This is the intended scalar application; its new
Lean specialization is not yet compiled. For the additional quantitative
half-measure clause use
[`MeasureTheory.mul_meas_ge_le_integral_of_nonneg`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean)
on `(0,τA)`, then finite-measure subtraction. Measurability, the a.e. physical
restart set and the zero-data branch remain explicit obligations.

## 9–10. Tail assembly and exact scope

The periodic [TailEnergy](../unpacked/METHBOKE_QFB_WFB_SOURCE_fdb515d8/Material/_vendor/QuasiFeffermanB/TailEnergy.lean)
and [TailUniqueness](../unpacked/METHBOKE_QFB_WFB_SOURCE_fdb515d8/Material/_vendor/QuasiFeffermanB/TailUniqueness.lean)
show the required order: identify the classical reference at every tail
time, identify weak gradients a.e. in time, transfer the energy integral,
and prove shifted-path membership before future uniqueness. On R³,
pointwise smoothness alone does not give finite-horizon Serrin control;
retain actual H¹ bounds or prove the needed integrability.

Methlib's
[`restricted_restart_class_eq_singleton`](../unpacked/METHLIB_QFA_ENDPOINTS_53b2318c/LeanEndpoints/QFA/Assembly/TailComparison.lean)
is reusable set/equality assembly after reference membership and fresh
comparison data have been supplied. The historical
[`QUASI_FEFFERMAN_A_CORRECTED`](../unpacked/METHLIB_QFA_ENDPOINTS_53b2318c/CorrectedPhysicalRoot/QFACorrectedRoot/PhysicalRoot.lean)
retains `ClassRealization`, `ReferencePorts`, `WholeSpaceSpectralEndpoint`,
`WholeSpaceAgmonEndpoint`, `CorrectedReferenceConstructionFromAbsorption`
and `SmoothReferencePorts`. Its standard axiom list does not discharge these
parameters. Its smoothness predicate is supplied, its cutoff is the older
one, and it does not separately state our tail energy equality.

Future uniqueness is always from each specified path's own exact trace.
For nonzero data, the current QFA target includes the closed safe cutoff
because the selected restart is strictly earlier. Zero data require the
separate zero-solution branch. QFB keeps its original strict main cutoff and
separate safe-cutoff clause. Neither construction asserts equality of the
tail traces of different original weak paths.

## Native endpoints to build next

These are **proposed names and scopes**, not existing declarations or proved
instances. Use a separate `MethbokeAddon.QuasiFeffermanA` namespace when
formalization is undertaken, so the historical QFA namespace keeps its meaning.

| Step | Proposed native endpoint | Exact completion requirement |
|---|---|---|
| 1 | `R3_LERAY_HOPF_CONTRACT` | Concrete all-L²σ data, weak gradient/momentum and representative semantics. |
| 2 | `R3_SPATIAL_ESTIMATES` | Actual H¹/H² spatial estimates with a proved admissible S; sharp specialization separately justified. |
| 3 | `R3_H1_LOCAL_AND_CONTINUATION` | Existence plus continuation for every actual H¹σ datum. |
| 4 | `R3_LH_EXISTS_AND_RESTARTS` | Global LH nonemptiness and a.e. physical admissible restart. |
| 5 | `R3_WEAK_STRONG_UNIQUENESS` | Same-trace physical comparison at every time. |
| 6 | `R3_SMALL_PRODUCT_GLOBAL_RESTART` | Actual balances, strict temporal margin and global continuation. |
| 7 | `R3_LH_WEIGHTED_ENERGY` | Extract `EnergyProfile` and apply the existing product-budget theorem. |
| 8 | `R3_GOOD_TIME_BEFORE_CUTOFF` | Current threshold/cutoff, half-measure estimate and zero branch. |
| 9 | `R3_CLOSED_TAIL_ENERGY` | Actual smooth velocity/pressure and energy equality including the safe cutoff. |
| 10 | `QUASI_FEFFERMAN_A_COMPOSED` | Existence, smooth tail, energy equality and same-trace unique future with all physical instances discharged. |

The immediate small integration package is the concrete representation/energy
contract and its adapters to the existing weighted-budget, generic-selector
and strong-trace results. The first substantial analytic requirements remain
the matching whole-space Sobolev/H¹ instance and actual R³ solution theory.
They are recorded as open rather than inserted as assumed fields and counted
as completed construction.

Passive `#check`/`#print axioms` files in this directory are preparation for
an authorized external environment only. They have not been executed and
are outside the active Material build. Compiler pins, dependencies, workflows,
accepted proof sources and the Fefferman-D program remain unchanged.
