# Weak_Fourierman_B: ten-endpoint source map v0.1

Date: 2026-11-19. Purpose: index-guided source reuse for the ten remaining contextual endpoints. This is an applicability register, not a new proof or compiler receipt. No Lean, Lake, Docker, installer, kernel audit, CI dispatch or repository mutation was performed.

The target remains the full finite squared Fourier budget on the same maximal strong trajectory implying an actual global smooth NSE solution, with same-path agreement. No universal finiteness claim is introduced.

## Scope, pins and evidence

Inspected the complete repository **tree inventories**, all fourteen Methboke endpoint manifests, `INDEX-WORTHY.txt`, the package/registry READMEs, and the selected theorem bodies below. A tree inventory is not a full audit of every source file. Negative findings are limited to the inspected material.

- Methboke: `43530b70d044624cbf83a3480840187a567549a5`.
- Methlib source provenance of the vendored endpoint packages: `96033dd69c994bec337a87369a6c27256e724980`.
- Additional Methlib comparison snapshot: `4813604a46179c745b82f51bee51a186e9f4cc2d`. Identical source blobs are recorded below; this snapshot is not substituted into the running container.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Existing external runtime/compiler pin remains Lean4.33.0. No runtime or payload was amended by this search.

The user's latest WFB diagnostic still reports accepted cached `PhysicalFourier` and repaired `FourierBudget`; original `LocalFront` failed. The repaired LocalFront and HomogeneousBudget have no supplied successful external results. This search does not change those statuses.

Methboke's endpoint JSON files retain historical preparation labels; the source-specific register and audits separately describe prior acceptance. In particular, the retained `material-73c2e98` QFBLerayHopf audit prints the exact Q01 type and only `propext`, `Classical.choice`, and `Quot.sound`. That historical evidence is not a fresh audit of a new WFB adapter.

## Ten-endpoint overview

| # | Target | Exact reusable source pieces | Remaining obligation |
|---:|---|---|---|
| 1 | Local-front Fourier to Serrin | `CRITICAL_SMOOTH_L6_FOURTH_BOUND`; `Integrable.mono'`; `integrable_norm_rpow_iff`; `lintegral_ofReal_ne_top_iff_integrable` | External acceptance of repaired finite-front measurability/energy/trace composition. |
| 2 | Homogeneous Fourier to Serrin | Actual energy/dissipation Parseval; `criticalSobolevLower_norm_le`; same Mathlib integrability primitives | External acceptance of prepared actual-slice composition. |
| 3 | Physical local existence | `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`; `finiteGalerkinRhs_uniform_local_time`; `CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE` | Cutoff-uniform physical local construction, initial regularity and pressure. Infinite RHS loses derivatives; fixed-cutoff ODE existence is insufficient. |
| 4 | Local strong uniqueness | `CRITICAL_RELATIVE_ENERGY_ZERO_OF_LOCAL_ADMISSIBLE_TRACE`; `CRITICAL_COMPARISON_EQ_OF_ADMISSIBLE_TRACE` | Derive the local physical relative-energy inequality and admissible traces; normalize pressure. |
| 5 | Maximal same-path trajectory | `IsIntegralCurveOn.mono`, time-translation identities, `zorn_le_nonempty`; local smooth gluing primitive | Define the physical extension order and prove chain upper bounds, local consistency and maximal lifetime. Generic ODE/Zorn results do not supply the PDE properties. |
| 6 | Physical endpoint continuation | `CUBIC_ENERGY_OF_SQUARE_BUDGET_EXACT_INITIAL`; `CUBIC_POSITIVE_TIME_ACCUMULATION`; existing spatial integration-by-parts/nonlinear estimates | Actual enstrophy evolution plus a physical local lifespan depending only on the controlled norm, then same-path restart. |
| 7 | Strict cutoff overlap | `CUTOFF_NONNEG`, `CUTOFF_POS`, `CUTOFF_ZERO`; `ENNReal.lt_iff_exists_real_btwn` | First prove `ofReal Tf < Tmax` by continuation/maximality. The finite overlap time then follows even for infinite lifetime. |
| 8 | Leray–Hopf identification | **`Q01_LERAY_HOPF_EXISTENCE` already constructs the weak path**; physical L2 embedding; `CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON` | Smooth-datum admission/trace wrapper and localization of the strong-reference hypotheses to the finite front. |
| 9 | Same-path tail and pressure gluing | `Q09_POST_CUTOFF_SMOOTHNESS`; Fourier coefficient a.e. congruence; continuous periodic Fourier injectivity; `contDiffOn_of_locally_contDiffOn` | Pointwise overlap agreement, normalized-pressure agreement, and a glued function satisfying all physical fields. |
| 10 | Weak_Fourierman_B root | Exact `GlobalSmoothNSE`; `globalSmoothNSE_zero`; composed QFB endpoint | Nonzero physical continuation/identification/gluing, zero-path uniqueness, all lifetime cases and matching external root audit. |

Endpoints1 and2 are alternative analytic routes, although the current HomogeneousBudget module imports LocalFront. Neither alone constructs or continues an NSE solution.

## Correction to the previous plan

Global weak existence should **not** be listed as an entirely new construction in endpoint8. `Q01_LERAY_HOPF_EXISTENCE` is present in the pinned closure and is used by `QUASI_FEFFERMAN_B_COMPOSED`. It supplies a genuine global physical weak path from `EnergySigmaZero` data. The new work is the smooth-datum adapter and finite-front weak–strong identification. The composed QFB result supplies eventual regularity, not the WFB global-smooth conclusion.

## 1. Local-front Fourier-to-Serrin

**Already suitable reusable mathematical identities.**

- `SingularClosure.CRITICAL_SMOOTH_L6_FOURTH_BOUND`, Methboke `Material/_vendor/SingularClosure/CriticalSerrinTime.lean:49`:
  `exists K>0, forall v, ContDiff R infinity v -> SpatialPeriodic v -> criticalSpatialNorm 6 v ^ 4 <= K*(9*physicalDissipation v^2 + physicalEnergy v^2)`.
  Applies to an arbitrary actual smooth periodic slice. It does not require a global solution wrapper.
- `MeasureTheory.lintegral_ofReal_ne_top_iff_integrable`, Mathlib `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:934`:
  AE strong measurability and AE nonnegativity of real f imply `(lintegral ofReal f != infinity) iff Integrable f`.
  Keeps finiteness substantive; a totalized real integral alone would not suffice.
- `MeasureTheory.Integrable.mono'`, same file:101: an integrable real dominator, AE strong measurability of f, and AE norm bound imply Integrable f.
- `MeasureTheory.integrable_norm_rpow_iff`, same file:225: with AE strong measurability and `p != 0, infinity`, integrability of `norm(f)^p.toReal` iff `MemLp f p`. Specialize p=4.
- `MeasureTheory.lintegral_const_mul'`, Mathlib `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:418`: finite nonnegative extended constant factors out of lintegral without a separate integrand measurability assumption.

These exact primitives occur in the repaired FourierBudget source; the user report accepts that five-endpoint layer as reused PASS_STANDARD_ONLY. Their composition with the actual finite-front measurability/energy/trace adapter remains pending in repaired LocalFront.

Useful localization blueprint, not directly usable with finite-front inputs:
`criticalPositive_spatialNorm_aestronglyMeasurable` in `CriticalSpatialNormMeasurable.lean:17` assumes a `CriticalPositiveSobolevFlow` (already a global positive-time flow). Its proof uses measurable piecewise extension and parameter lintegral measurability. The current local-front source localizes that proof; quoting the original endpoint would import a globality premise.

## 2. Homogeneous Fourier-to-Serrin

**Exact identity chain found in pinned source.**

- `critical_smoothFourierSynthesis_energy_eq_norm_sq`, `CriticalSmoothEnergyNorm.lean:16`:
  rapid coefficient family, spectral reality, and matching `CriticalSobolev 0` representative imply physical energy of its actual smooth synthesis equals the representative norm squared.
- `critical_smoothFourierSynthesis_dissipation_eq_norm_sq`, `CriticalSmoothParseval.lean:79`:
  rapid coefficients, spectral reality, spectral mean zero, matching `CriticalSobolev 2` representative imply physical dissipation equals its norm squared. Critical order2 is H1.
- **Located exact contraction source:** `criticalSobolevLower_norm_le`, `CriticalSpacesEmbedding.lean:81`:
  for integers q<=r and `c : CriticalSobolev r`, `norm(criticalSobolevLower q r hqr c) <= norm c`.
  With q=0,r=2 and actual Fourier reconstruction, this yields `E(v)<=D(v)` for the same mean-zero smooth periodic field.
- Combine with `CRITICAL_SMOOTH_L6_FOURTH_BOUND` to obtain `L6(v)^4 <= 10*K*D(v)^2`.
- Reuse the Mathlib domination and rpow/MemLp equivalence from endpoint1 for time integration.

`CriticalPositiveSobolevFlow.physicalEnergy_le_dissipation` (`CriticalHomogeneousL6.lean:16`) and `CRITICAL_POSITIVE_HOMOGENEOUS_L6_FOURTH` (`:34`) are existing proof blueprints, but their statements require a global positive-time flow. The prepared HomogeneousBudget module correctly reconstructs the slice-level argument instead of assuming such a flow.

Remaining: accept the prepared local proof against the external pinned compiler and audit. These identities establish the analytic budget-to-Serrin implication, not physical continuation or existence.

## 3. Actual physical local existence

1. Mathlib/Analysis/ODE/ExistUnique.lean:57:
   IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt.
   E is a complete real normed space; vector field has type R -> E -> E.
   The full IsPicardLindelof bounds and closed-ball membership give a trajectory
   with the actual derivative equation and initial point on Icc.
   Same-space Banach ODE existence primitive, not a physical NSE theorem.

2. Same file:145:
   ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt.
   C1 same-space autonomous vector field near a point yields positive radius/time,
   locally uniform over a closed starting ball. Useful for a verified bounded
   RHS realization, but raw NSE loses derivatives.

3. Methboke Material/_vendor/SingularClosure/GalerkinExistence.lean:27:
   finiteGalerkinRhs_local_exists nu N z0 t0.
   Any finite state has a local actual finite Fourier ODE solution.
   :39 finiteGalerkinRhs_uniform_local_time nu N R.
   Quantifier order is forall nu,N,R, exists delta>0, forall starting states in
   closedBall(0,R), forall t0, exists actual ODE solution for delta.
   delta can depend on N. Its proof uses compactness of the finite-dimensional
   closed ball; this does not supply a common physical H1 lifespan.

4. Methboke Material/_vendor/SingularClosure/CriticalGalerkin.lean:124:
   CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE.
   nu>=0, SpectralReality c, SpectralSolenoidal c, finite cutoff N:
   exists g : GalerkinSolution nu (finiteSynthesis N c) N, initial coefficients
   equal cutoffCoeff N c, and forward uniqueness among these Galerkin solutions.
   This is a genuine existence/uniqueness theorem, at fixed cutoff.

5. Methboke Material/_vendor/SingularClosure/FourierSobolevRhs.lean:
   :117 fourierSobolevRhs : TorusSobolev(r+2) -> TorusSobolev r.
   :120 fourierSobolevRhs_contDiff.
   :130 fourierSobolevRhs_coefficient_eq_fullRhs.
   These provide the actual infinite RHS, smoothness between scales, and its
   coefficient identity; they do not yield a same-space Picard vector field.

6. PhysicalNSE/endpoint.json indexes CRITICAL_POSITIVE_PHYSICAL_NSE,
   CriticalPositiveSobolevFlow.velocity_spacetime_smooth,
   CriticalPositiveSobolevFlow.pressure_spacetime_smooth.
   Exact declared scope: existing all-order positive-time Sobolev flow required;
   arbitrary-data existence is not asserted.

Unresolved specialization:
actual finite-horizon physical construction from smooth datum, with initial
regularity, pressure, periodicity and divergence constraints; or an independently
proved local H1 construction uniform on bounded H1 states for continuation.
Fixed-cutoff existence plus convergence requires new cutoff-uniform estimates.

## 4. local strong uniqueness

Index entry: `Material/RelativeEnergy/endpoint.json`.

Direct scalar component:
`SingularClosure.CRITICAL_RELATIVE_ENERGY_ZERO_OF_LOCAL_ADMISSIBLE_TRACE`
in `SingularClosure/CriticalLocalUniqueness.lean:17`.
It assumes nonnegative relative energy, a continuous nonnegative coefficient,
its finite integral budget, local integrability of coefficient times energy,
admissible positive times tending to zero, vanishing relative-energy trace,
and the Volterra inequality. It concludes energy zero at every time in
`Ioc 0 T`.

Other reusable scalar identities:
`CRITICAL_RELATIVE_ENERGY_GRONWALL` and
`CRITICAL_COMPARISON_EQ_OF_ADMISSIBLE_TRACE` in
`SingularClosure/CriticalUniqueness.lean`.
The latter directly turns a norm-square relative-energy inequality and a
common strong trace into equality in a normed space.

Remaining PDE work: derive the finite-front cross-testing/relative-energy
inequality for the concrete two local strong solutions and verify all trace
and coefficient-integrability premises. Pressure equality requires its
normalization adapter; a scalar Gronwall lemma alone is not NSE uniqueness.

## 5. Maximal same-path trajectory

Concrete Mathlib primitives found at the pinned revision:
- Mathlib/Analysis/ODE/Basic.lean:98 IsIntegralCurveOn.mono (restriction).
- :106 IsIntegralCurveOn.isIntegralCurveAt (on a neighborhood -> local property).
- :110 IsIntegralCurveAt.isIntegralCurveOn (local properties -> on-set property).
- :116 isIntegralCurveOn_iff_isIntegralCurveAt for an open time set.
- Mathlib/Analysis/ODE/Transform.lean:37 IsIntegralCurveOn.comp_add;
  :59 IsIntegralCurveOn.comp_sub (time translation/restart).
- Mathlib/Order/Zorn.lean:103 zorn_le; :106 zorn_le_nonempty;
  :110 zorn_le₀. A preorder whose chains have upper bounds has a maximal element.

Potential assembly, explicitly not supplied by these lemmas:
define the physical solution extension preorder; supply a nonempty family from
local existence; prove chain unions carry the same well-defined physical
solution, normalized pressure and initial data using local uniqueness; obtain
a maximal member and identify its interval/lifetime in extended nonnegative
reals. The PDE constraints, chain upper bounds and uniqueness glue remain to
prove. Generic Zorn does not certify them. The ODE primitives require a valid
same-space realization; they can directly organize finite Fourier approximants,
or guide analogous pointwise PDE lemmas.

No ready-made physical maximal-NSE construction was located in the inspected
indexed sources. This is not a claim about every possible uninspected repository.

## 6. Physical endpoint continuation

Most concrete reusable scalar identity:
Methboke Material/_vendor/SingularClosure/CubicBudget.lean:174
CUBIC_ENERGY_OF_SQUARE_BUDGET_EXACT_INITIAL:
nu>0, kappa>=0, T>=0, M>=0; y,z,d continuous on [0,T]; y>=0;
y'=d on (0,T); d+nu*z^2 <= kappa*y^3; integral_0^T y^2 <= M
implies y(t)+nu*integral_0^t z^2 <= y(0)*exp(kappa*M).
The input z is the square-root dissipation quantity (e.g. ||Delta u||_2),
so z^2 is the physical Laplacian-square dissipation.
Apply on compact subintervals before a possible endpoint; do not assume an
endpoint trace/continuity to derive continuation.

Material/_vendor/SingularClosure/CriticalPositiveTimeScalar.lean:31
CUBIC_POSITIVE_TIME_ACCUMULATION:
same scalar hypotheses, 0<tau<=T, yields for t in [tau,T]:
y(t)+nu*integral_tau^t z^2 <= sqrt(M/tau)*exp(kappa*M).
Can support positive-time bounds after a time-shift/localization.

Material/_vendor/SingularClosure/StrongAccumulation.lean:66
AX6_UNIFORM_ENSTROPHY_ACCUMULATION;
UniformStrongBounds.lean:65 AX6_UNIFORM_PHYSICAL_STRONG_BOUNDS;
StrongSobolevRealization.lean:63 AX6_UNIFORM_STRONG_BOUNDS.
These are real physical/Galerkin norm adapters but explicitly take
hAX6 : AX6Statement. One actual solution's Fourier budget does not establish
the required uniform budget for all Galerkin solutions.

Still required for the constructive route:
(a) arbitrary physical-field enstrophy differential inequality,
(b) uniform bound from the scalar identity,
(c) physical local H1 lifespan depending only on nu and that bound,
(d) uniqueness to match a restart near T to the same trajectory.
The endpoint is not closed by the scalar identities alone.

## 7. Strict cutoff overlap

**New exact order-theoretic match avoids an infinity conversion trap.**

`ENNReal.lt_iff_exists_real_btwn`, Mathlib `Mathlib/Data/ENNReal/Basic.lean:589`:

```
a < b <-> exists r : R, 0 <= r and
  a < ENNReal.ofReal r and ENNReal.ofReal r < b
```

Set `a = ENNReal.ofReal Tf`, `b = Tmax`. Once the physical continuation/maximality argument has established `ofReal Tf < Tmax`, this directly provides a finite real overlap time delta even when `Tmax=infinity`.

`ENNReal.ofReal_lt_ofReal_iff_of_nonneg`, `Mathlib/Data/ENNReal/Real.lean:171`, needs `0<=Tf` and turns `ofReal Tf < ofReal delta` into `Tf<delta`.

Other verified primitives:
- `exists_between`, `Mathlib/Order/Basic.lean:977`: any densely ordered type; directly useful after reducing to a finite real lifetime.
- `ENNReal.ofReal_lt_top`, `Mathlib/Data/ENNReal/Basic.lean:346`: finite real cutoff has finite extended image.
- `ENNReal.toReal_ofReal`, same file:250: requires nonnegative real input.
- `ENNReal.toReal_lt_toReal`, `Mathlib/Data/ENNReal/Real.lean:76`: requires BOTH extended inputs unequal to infinity.
- `ENNReal.toReal_min`, same file:113: also requires BOTH inputs finite, so it must not be applied directly to `min Tmax (ofReal Tf)` when Tmax may be infinity.

Define extended tau as `min Tmax (ofReal Tf)`; its finiteness follows from domination by `ofReal Tf`. Only tau can be converted toReal unconditionally after this proof. Either use the direct real-between theorem for overlap or split finite/infinite Tmax first.

Remaining analytic obligation: derive `ofReal Tf < Tmax` from the full budget and continuation. These order lemmas cannot provide it. Zero datum/zero cutoff must be handled separately; positivity of the physical datum norm for a nonzero smooth periodic field must be justified by the physical realization, not treated as pointwise-function norm positivity.

The pinned `QuasiFeffermanB/Cutoff.lean` also directly proves:
`CUTOFF_NONNEG` for positive viscosity; `CUTOFF_ZERO`; `CUTOFF_POS` for nonzero physical L2 datum and positive viscosity; `SAFE_CUTOFF_GT`; and `ENERGY_SLICE_CUTOFF`, which rewrites the cutoff as `E^2/(2*pi^2*nu^5)` when `E=norm(a)^2/2`. These are scalar identities only. The physical representative's nonzeroness must be shown from the smooth periodic datum before applying `CUTOFF_POS`.


## 8. weak–strong identification

Index entry: `Material/SerrinComparison/endpoint.json` explicitly warns that
the existing reference hypotheses quantify over all positive times.

`SingularClosure.CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON` in
`SingularClosure/CriticalSerrinUniqueness.lean:37` assumes:

- positive viscosity;
- an actual global `CriticalLerayHopf ν a₀ v G`;
- `CriticalPositiveSolenoidalTest u` (joint smoothness on all positive times);
- pressure smoothness/periodicity and physical NSE for every positive time;
- strong common physical L2 trace at zero;
- finite-horizon time-L4 spatial-L6 norm on `Ioc 0 T`.

It proves `v t =ᵐ[volume.restrict unitCube] u t` for every `t ∈ Ioc 0 T`.
This is exactly the desired physical equality notion, but the strong-reference
hypotheses must be localized before using it before a possible maximal endpoint.

Useful proof components already used by this theorem:

- `CRITICAL_ROUGH_TRANSPORT_ENERGY_BOUND`,
  `criticalSerrinEnergyCoefficient_integrable`, in
  `CriticalGradientEnergyBound.lean`: transport absorbed by gradient energy,
  with integrable coefficient proportional to `U^4/ν^3 + U^2/ν`.
- `CRITICAL_LH_SMOOTH_RELATIVE_ENERGY_TRANSPORT`,
  `CRITICAL_RELATIVE_ENERGY_PRODUCT_INTERVAL_INTEGRABLE`,
  `CRITICAL_ADMISSIBLE_TIMES_TENDSTO_ZERO` are named dependencies in the
  inspected comparison proof. Their own signatures must be read when
  implementing the finite-front adapter.

### Smooth datum to Q01 admission: concrete existing pieces

Set `a₂ := physicalFieldL2 a ha.smooth.continuous`.

- `CriticalCubeL2.lean:69`: `physicalFieldL2` is the genuine physical cube
  L2 representative of any continuous field.
- `CriticalCubeL2.lean:72`: `physicalFieldL2_coe` gives a.e. equality with a.
- `CriticalCubeL2.lean:76`: `physicalFieldL2_norm_sq` gives
  `‖a₂‖² = physicalEnergy a`.
- `CriticalSmoothCancellation.lean:17`:
  `critical_smooth_integral_inner_gradient_eq_zero` gives
  `∫cube inner a (gradient f)=0` for smooth periodic solenoidal a and smooth
  periodic f. There is no Galerkin restriction.
- `QuasiFeffermanB/MeanPreservation.lean:15`:
  `physical_inner_congr_left_ae` transfers physical pairings along a.e.
  representative equality.
- The `EnergySigmaZero.mean_zero` component becomes the corresponding
  component of `SmoothSigmaZero.mean_zero`, using inner product with the
  coordinate unit vector and the integral definition of MeanZero.

These components support a short new wrapper
`SmoothSigmaZero a → EnergySigmaZero a₂`; no exact wrapper with this name is
claimed to have been found. Also transfer the initial strong trace to a₂.

For the exact cutoff, `CriticalGradientEnergyBound.lean:27`
`critical_velocity_L2_toReal_sq_eq_physicalEnergy` gives
`((eLpNorm a 2 cube).toReal)^2 = physicalEnergy a`.
Together with `physicalFieldL2_norm_sq`, squaring identifies both fourth powers.
`QuasiFeffermanB/Semantics.lean:42` then has exactly
`cutoff a₂ ν = ‖a₂‖^4/(8*pi^2*ν^5)`.

## 9. same-path QFB tail and pressure-compatible gluing

The exact existing tail result is
`QuasiFeffermanB.Q09_POST_CUTOFF_SMOOTHNESS` in
`QuasiFeffermanB/TailChain.lean:13`:
`ν>0`, `EnergySigmaZero a₂`, `CriticalLerayHopf ν a₂ v G`,
`cutoff a₂ ν < δ` imply `HasSmoothTail ν v δ`.
This is for the same supplied v, not an unrelated existential solution.

`QuasiFeffermanB/RootContract.lean:18` defines ClassicalTail with actual
joint smoothness, periodic velocity/pressure, divergence zero, NSE,
velocity mean zero and normalized mean-zero pressure.
`HasSmoothTail` at line31 supplies a classical pair `(w,p)` and
`∀t≥δ, v t =ᵐ[cube] w t`.

Other exact existing tail pieces:

- `Q11_POST_CUTOFF_ENERGY_EQUALITY` (TailChain:21).
- `Q12_POST_CUTOFF_TRACE_UNIQUENESS` (TailChain:29).
- `CLASSICAL_TAIL_OF_POSITIVE_SMOOTH_NSE`
  (`TailRegularity.lean:39`) correctly translates physical time derivatives.
- `LH_UNIQUE_FUTURE_OF_SMOOTH_REFERENCE`
  (`TailUniqueness.lean:149`) and
  `positive_reference_strict_shift_serrin` (same file:60).
  These still require the existing global positive-time reference and
  same-path agreement, so they are not substitutes for finite-front comparison.

For upgrading overlap velocity equality from a.e. to pointwise:

1. `criticalCube_datumFourierCoeff_congr_ae`
   (`CriticalInitialPhysicalFourier.lean:55`) makes actual Fourier coefficients
   equal from cube a.e. equality.
2. `datumFourierCoeff_injective_continuous_periodic`
   (`PeriodicFourierInjective.lean:77`) makes continuous periodic fields equal
   pointwise from that coefficient identity.

These already-existing identities avoid pretending cube-a.e. equality alone
is pointwise equality on all of R³.

Pressure construction components:
`fullTransportPressure_meanZero` (`InfiniteFourierPressure.lean:250`) and
`INFINITE_TRANSPORT_PRESSURE_RECOVERY` (same file:267) give an actual smooth,
periodic, mean-zero pressure and the exact transport/Leray recovery identity,
under all-Sobolev membership plus spectral reality and solenoidality.
`CRITICAL_POSITIVE_PRESSURE_JOINT_SMOOTH`
(`CriticalPositivePressure.lean:39`) supplies joint smoothness from compatible
smooth Sobolev curves.

Still required: an arbitrary normalized-pressure uniqueness lemma on the
overlap, local equality of physical derivatives, and a concrete smooth
front/tail gluing theorem preserving initial regularity and all GlobalSmoothNSE
fields. No ready-made WFB pressure-gluing theorem was located in the inspected
indexes and pressure files. This is a bounded search finding, not a claim
that no such theorem exists anywhere in Mathlib/Methlib.

Mathlib `Mathlib/Analysis/Calculus/ContDiff/Defs.lean:587` provides the exact local-to-global smoothness primitive `contDiffOn_of_locally_contDiffOn`: for one already-defined function f on s, local smoothness on each `s ∩ u` for an open neighborhood u gives `ContDiffOn f s`. After constructing a single front/tail function and proving equality on the overlap, this handles smoothness locally. It does not construct the overlap or prove pressure agreement.


## 10. Root zero case and assembly

`SingularClosure.globalSmoothNSE_zero`, Methboke `Material/_vendor/SingularClosure/Contracts.lean:130`:

```
forall nu : R,
 GlobalSmoothNSE nu (0 : Field) (0 : Velocity) (0 : Pressure)
```

This is a genuine proved source witness, independent of a positive-viscosity premise. `smoothSigmaZero_zero` at:121 supplies admissibility of the zero datum.

`GlobalSmoothNSE` at:96 is the exact four-argument physical predicate. Required fields include joint velocity AND pressure smoothness on forwardSpacetime, periodicity, divergence zero, pointwise physical PDE for every t>=0, initial datum, velocity mean zero, and normalized pressure.

Reuse limit: `globalSmoothNSE_zero` discharges existence for the zero case, but agreement with an already-given maximal zero-data path still requires uniqueness. For nonzero data, root assembly remains dependent on actual maximal-path construction, finite-endpoint continuation, weak-strong identification and compatible gluing. No root theorem is found or asserted by this source map.

## Indexed matches that cannot be substituted for continuation

Methlib regularity-B-assembly/pkg2/CEA10_CriticalToRegularity.lean:7-20:
CriticalToRegularityCertificate explicitly contains
  regular_of_serrin46 : Serrin46 -> Regular.
CEA_theta_criticalPair_to_regular projects this assumed implication after
scalar interpolation. It does not prove physical endpoint continuation.

Methlib regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/
CriticalGlobalSerrin.lean:69:
CriticalRegularSolution.serrin_global_memLp_of_quartic_budget starts with
U : CriticalRegularSolution nu a and a uniform quartic budget. It proves global
Serrin membership for an already-existing regular solution, not extension.

Methlib regularity-B-assembly/REGULARITY_FRONT/S_DIR_L2_GLOBAL_REGULARITY.lean:
:72 AnalyticEndpointCertificates explicitly leaves physical heat synthesis,
Serrin and weak-strong uniqueness as certificate fields.
:100 S_DIR_L2_GLOBAL_REGULARITY_of_certificates assumes those fields.
:117 S_DIR_L2_GLOBAL_REGULARITY_FOURIER_M7_UNCONDITIONAL proves Fourier flux zero
only. Its name does not make the physical root unconditional.

## Cross-repository identity

The pinned Methlib Singular-Axiomatic-closure/SingularClosure copies have exactly
the same Git blobs as pinned Methboke's vendored sources:
GalerkinExistence.lean 99a1d77891985e082e015e055cef7c3980c2e5fc
FourierSobolevRhs.lean d1744699f89f77177fb5cb598e67e04fbad28749
CubicBudget.lean 7cc2dd0e9976dd08123b18aab76928f3fcbbe4d5
CriticalPositiveTimeScalar.lean 226f08c662a4976466e9285892ba3ff075a32b60

The MathlibODE/Galerkin README indexes report external pass at older exact
source6440270... with retained audits. Endpoint.json still says prepared
PENDING_EXTERNAL_CI; it is provenance, not latest acceptance. The retained registry/audit evidence is described above; this source map makes no new compiler-pass claim.

## Pinned source links

- [Primary result index](https://github.com/randogelist/Methboke/blob/43530b70d044624cbf83a3480840187a567549a5/INDEX-WORTHY.txt)
- [Material endpoint inventory](https://github.com/randogelist/Methboke/blob/43530b70d044624cbf83a3480840187a567549a5/Material/README.md)
- [Q01 actual weak existence](https://github.com/randogelist/Methboke/blob/43530b70d044624cbf83a3480840187a567549a5/Material/_vendor/QuasiFeffermanB/Endpoints/LerayHopfExistence.lean)
- [Q01 retained type/axiom audit](https://github.com/randogelist/Methboke/blob/43530b70d044624cbf83a3480840187a567549a5/audits/material-73c2e98/audits/QFBLerayHopf-b3be6a297bab0ebe2efe14b5c171dd5a70952861c1716c62b124e1c0a482dab1.log)
- [QFB same-path tail](https://github.com/randogelist/Methboke/blob/43530b70d044624cbf83a3480840187a567549a5/Material/_vendor/QuasiFeffermanB/TailChain.lean)
- [QFB tail semantics](https://github.com/randogelist/Methboke/blob/43530b70d044624cbf83a3480840187a567549a5/Material/_vendor/QuasiFeffermanB/RootContract.lean)
- [Actual slice Sobolev bound](https://github.com/randogelist/Methboke/blob/43530b70d044624cbf83a3480840187a567549a5/Material/_vendor/SingularClosure/CriticalSerrinTime.lean)
- [Sobolev norm contraction](https://github.com/randogelist/Methboke/blob/43530b70d044624cbf83a3480840187a567549a5/Material/_vendor/SingularClosure/CriticalSpacesEmbedding.lean)
- [Finite-front scalar uniqueness](https://github.com/randogelist/Methboke/blob/43530b70d044624cbf83a3480840187a567549a5/Material/_vendor/SingularClosure/CriticalLocalUniqueness.lean)
- [Physical weak-strong comparison](https://github.com/randogelist/Methboke/blob/43530b70d044624cbf83a3480840187a567549a5/Material/_vendor/SingularClosure/CriticalSerrinUniqueness.lean)
- [Square-budget scalar estimate](https://github.com/randogelist/Methboke/blob/43530b70d044624cbf83a3480840187a567549a5/Material/_vendor/SingularClosure/CubicBudget.lean)
- [Physical contract and zero witness](https://github.com/randogelist/Methboke/blob/43530b70d044624cbf83a3480840187a567549a5/Material/_vendor/SingularClosure/Contracts.lean)
- [Finite-cutoff local existence](https://github.com/randogelist/Methboke/blob/43530b70d044624cbf83a3480840187a567549a5/Material/_vendor/SingularClosure/GalerkinExistence.lean)
- [Generic Banach ODE existence](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/ODE/ExistUnique.lean)
- [Integrability and MemLp primitives](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean)
- [Extended lifetime real-between identity](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/ENNReal/Basic.lean)
- [Local smooth gluing primitive](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/ContDiff/Defs.lean)
- [Generic maximality principle](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Order/Zorn.lean)

## Next scope after this lookup

The most contained new adapter targets are: smooth datum to `EnergySigmaZero` with the exact norm/cutoff identity; finite-front localization of physical weak–strong comparison; and normalized-pressure overlap/gluing. These can be specified against an explicit finite front without assuming global regularity. Physical local existence, actual maximal-path construction, and endpoint continuation remain substantive obligations. No root conclusion follows until those edges are proved and the resulting exact theorem receives matching external compilation/type/axiom evidence.
