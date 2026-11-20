# Steps 7–10: exact scalar and tail anchors

Static source and retained-evidence review only. No compiler/kernel execution, no new formalization and no new QFA root acceptance.

## Current finding

The recovered QFA branch contains the **exact sharp weighted product budget**, including an instance on actual full-volume spatial L2 norm data. Its generic selector, trace, restart-data and tail-comparison declarations have matching retained named compiler types and axiom logs. The current numeric cutoff/half-measure wrapper and actual whole-space solution, pressure, energy-transfer and comparison realizations remain separate obligations.

## Source and evidence identities

- Periodic reference: Methboke `fdb515d8bde35ec8021bbc26f360aca8dfa2855c`, vendored Methlib `96033dd69c994bec337a87369a6c27256e724980`; retained run `44566880192`, artifact `14553501775`. Existing Linux evidence is not native-Windows evidence.
- Recovered QFA: Methlib `53b2318c2b586137b6db74c4d3a41bb0b964b2d8`. All 34 files in the historical source/configuration manifest match raw SHA256. Retained compiled commit `9b6ca616b2f26e0222decb872401752e8320babe`, native Windows run `43532773061`, Lean 4.33.0. The record retains 108 exact declaration types and axiom sets; all use only `propext`, `Classical.choice`, `Quot.sound`.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d` for both source tracks.
- Corrected root: source at the recovered commit plus retained `41188cef6ac21628648e0e2b598d926604d9813f` named axiom/status summaries. The reviewed record has no full exact compiler-type/axiom transcript; keep this evidence distinct.

Source-header candidate labels predate retained evidence. Matching historical evidence supports the exact implication that was checked; it does not discharge assumptions in its type.

## Findings by step

### Step 7

QFA.Energy.product_budget and product_budget_Ioo prove the exact weighted /4nu bound, including actual product integrability and residual square. QFA.Representation.EnergyProfile.energy_product_budget_Ioo instantiates this on full-volume L2(R3;R3) norm data. Matching retained named compiler types and standard-only axiom logs exist.

Actual LH realization still supplies the EnergyProfile and weak-gradient identification. There is no need to assume continuity or differentiate weak energy E.

Prior periodic-only search correctly found only LH_ENERGY_BOUNDS and criticalFourthPower_budget with unweighted/frozen /2nu bounds. That limitation is not a global absence claim and is superseded for generic step7 by the recovered QFA proof.

### Step 8

QFA.Endpoints.GoodTime.exists_good_time_of_integral_lt is an exact audited generic selector on volume.restrict(Ioo 0 T), retaining arbitrary a.e. Good. Existing QFA specialized selectors and strong-trace composition use the historical 4*pi^2 threshold and strict 16*pi^2 cutoff.

For the current nonzero branch use f=E*Y,c=theta,T=tauA and budget<=theta*tauA/2<theta*tauA. The quantitative half-measure clause uses the pinned Mathlib Markov and measure-subtraction anchors; no current-constant or half-measure wrapper was located. Actual LH full-measure H1/energy-start/PDE restart facts remain required.

Zero datum has tauA=0 and must be handled separately by nonnegative-energy norm rigidity; the archived strict-cutoff wrapper does not provide the closed zero endpoint.

### Step 9

QFA.Assembly.TailComparison supplies equality on the closed normed-carrier tail from relative-energy comparison. CorrectedPhysicalRoot.selectedTail_smooth transfers a supplied semantic SmoothNSETail predicate at positive reference time delta-s. The periodic tail-energy chain remains a concrete pattern, not a whole-space implementation.

Actual R3 smooth representatives, pressure/NSE semantics, equality of weak gradients on a.e. time slices, spatial energy identity/integrability and its transfer to the LH path still need supplying. SmoothReferencePorts does not prove those facts. s<tauA places the closed positive cutoff inside the reference smooth regime; no arbitrary weak-gradient point value at delta is needed.

Corrected-root retained axiom/status summaries are not a full compiler-type transcript. Periodic energy proofs use periodic geometry and cannot be transplanted by a carrier rename.

### Step 10

QFA provides exact named audited Hilbert trace, time-translation, norm-profile restart, finite-horizon comparison and restricted-singleton composition. ClassRealization, reference construction and comparison/admission ports remain explicit in the archived root assembly; CorrectedPhysicalRoot keeps the remaining analytic and semantic premises.

RestartData proves only translated energy profile, weak pairing continuity and strong trace; actual LH restart needs translated momentum, divergence and weak gradients. Future uniqueness compares every admissible continuation from the same exact u(delta), includes initial values separately from right traces, and restricts equality to nonnegative time. On R3 a finite-horizon Serrin/relative-energy bound must come from H1 or proved integrability; positive smoothness alone is insufficient.

The archived QFA root uses the old cutoff and remains conditional. Accepted periodic QUASI_FEFFERMAN_B_COMPOSED keeps its literal retained audit and is the reference, not proof of the new whole-space root.

## Constants and endpoints

Current target: S6^6 = 16/(27*pi^4), theta = nu^4/S6^6, tauA = S6^6*||a||2^4/(2*nu^5) = 8*||a||2^4/(27*pi^4*nu^5). The weighted budget is integral E*Y <= ||a||2^4/(4*nu) = theta*tauA/2. For nonzero data this gives strict-average selection before tauA; Markov plus finite-interval measure subtraction gives good-set measure at least tauA/2.

Historical QFA wrappers instead select E*D < 4*pi^2*nu^4 assuming delta > ||a||2^4/(16*pi^2*nu^5). Their constants and strict endpoint remain visible. The zero branch requires a separate norm-rigidity argument at tauA=0.

## Exact source anchors

The JSON retains full source signatures, reviewed proof excerpts, raw hashes, exact imports, source identities, cached compiler types and log line locations where available. Line spans below describe declaration/proof bodies, not a claim that every anchor has equal evidence.

| ID | Declaration | Source | Reuse and evidence |
|---|---|---|---|
| S07-01 | `QuasiFeffermanB.LH_ENERGY_BOUNDS` | `Material/_vendor/QuasiFeffermanB/LHEnergy.lean`:14–32 | PERIODIC_INSTANCE; module receipt only; no individual named audit located |
| S07-02 | `QuasiFeffermanB.criticalFourthPower_budget` | `Material/_vendor/QuasiFeffermanB/CriticalTimeBudget.lean`:42–62 | DOMAIN_NEUTRAL_WEAKER_BOUND; module receipt only; no individual named audit located |
| S07-03 | `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral` | `Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`:412–454 | DOMAIN_NEUTRAL_EXACT; pinned Mathlib source; no separate new audit |
| S07-04 | `IntervalIntegrable.ae_hasDerivAt_integral` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`:66–84 | DOMAIN_NEUTRAL_EXACT; pinned Mathlib source; no separate new audit |
| S07-05 | `AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`:245–254 | DOMAIN_NEUTRAL_EXACT; pinned Mathlib source; no separate new audit |
| S07-06 | `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`:257–265 | DOMAIN_NEUTRAL_EXACT; pinned Mathlib source; no separate new audit |
| S07-07 | `IntervalIntegrable.continuousOn_mul` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`:355–358 | DOMAIN_NEUTRAL_EXACT; pinned Mathlib source; no separate new audit |
| S07-08 | `intervalIntegral.integral_mono_ae_restrict` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`:1424–1427 | DOMAIN_NEUTRAL_EXACT; pinned Mathlib source; no separate new audit |
| S07-09 | `SingularClosure.CRITICAL_SQUARE_BUDGET_DIV` | `Material/_vendor/SingularClosure/CriticalInvariant.lean`:174–194 | DOMAIN_NEUTRAL_STRONGER_HYPOTHESES; module receipt only; no individual named audit located |
| S08-01 | `QuasiFeffermanB.exists_good_time_of_integral_lt` | `Material/_vendor/QuasiFeffermanB/GoodTime.lean`:12–35 | DOMAIN_NEUTRAL_EXACT; module receipt only; no individual named audit located |
| S08-02 | `MeasureTheory.mul_meas_ge_le_integral_of_nonneg` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`:1129–1140 | DOMAIN_NEUTRAL_EXACT; pinned Mathlib source; no separate new audit |
| S08-03 | `MeasureTheory.measure_sdiff` | `Mathlib/MeasureTheory/Measure/MeasureSpace.lean`:250–251 | DOMAIN_NEUTRAL_EXACT; pinned Mathlib source; no separate new audit |
| S08-04 | `QuasiFeffermanB.LH_RESTART_AE_Ioo` | `Material/_vendor/QuasiFeffermanB/LHRestart.lean`:312–324 | PERIODIC_INSTANCE; literal named retained type/axiom audit |
| S08-05 | `QuasiFeffermanB.LH_GOOD_SUBCRITICAL_TIME` | `Material/_vendor/QuasiFeffermanB/GoodTime.lean`:73–105 | PERIODIC_INSTANCE; literal named retained type/axiom audit |
| S08-06 | `QuasiFeffermanB.ZERO_LH_VELOCITY` | `Material/_vendor/QuasiFeffermanB/ZeroData.lean`:15–37 | PERIODIC_INSTANCE_WITH_REUSABLE_NORM_ARGUMENT; module receipt only; no individual named audit located |
| S09-01 | `QuasiFeffermanB.HAS_SMOOTH_TAIL_OF_POSITIVE_REFERENCE` | `Material/_vendor/QuasiFeffermanB/TailRegularity.lean`:67–77 | PERIODIC_INSTANCE; module receipt only; no individual named audit located |
| S09-02 | `QuasiFeffermanB.physicalH1_gradient_eq_smooth` | `Material/_vendor/QuasiFeffermanB/TailEnergy.lean`:102–115 | PERIODIC_INSTANCE; module receipt only; no individual named audit located |
| S09-03 | `QuasiFeffermanB.physicalH1_gradientEnergy_eq_smooth` | `Material/_vendor/QuasiFeffermanB/TailEnergy.lean`:128–136 | PERIODIC_INSTANCE; module receipt only; no individual named audit located |
| S09-04 | `SingularClosure.CRITICAL_SMOOTH_NSE_ENERGY_IDENTITY` | `Material/_vendor/SingularClosure/CriticalSmoothEnergy.lean`:216–248 | PERIODIC_INSTANCE; module receipt only; no individual named audit located |
| S09-05 | `intervalIntegral.integral_congr_ae_restrict` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`:1257–1260 | DOMAIN_NEUTRAL_EXACT; pinned Mathlib source; no separate new audit |
| S09-06 | `intervalIntegral.integral_comp_sub_right` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`:1050–1051 | DOMAIN_NEUTRAL_EXACT; pinned Mathlib source; no separate new audit |
| S09-07 | `QuasiFeffermanB.LH_TAIL_ENERGY_OF_POSITIVE_REFERENCE` | `Material/_vendor/QuasiFeffermanB/TailEnergy.lean`:153–186 | PERIODIC_INSTANCE; module receipt only; no individual named audit located |
| S10-01 | `QuasiFeffermanB.strong_tendsto_of_inner_and_norm_bound` | `Material/_vendor/QuasiFeffermanB/LHRestart.lean`:71–95 | DOMAIN_NEUTRAL_EXACT; module receipt only; no individual named audit located |
| S10-02 | `QuasiFeffermanB.timeTranslate_memLp_Ioc` | `Material/_vendor/QuasiFeffermanB/TimeTranslate.lean`:176–185 | DOMAIN_NEUTRAL_EXACT; module receipt only; no individual named audit located |
| S10-03 | `QuasiFeffermanB.timeTranslate_ae_Ioc` | `Material/_vendor/QuasiFeffermanB/TimeTranslate.lean`:187–201 | DOMAIN_NEUTRAL_EXACT; module receipt only; no individual named audit located |
| S10-04 | `QuasiFeffermanB.LH_RESTART_FROM_ENERGY_START` | `Material/_vendor/QuasiFeffermanB/LHRestart.lean`:215–276 | PERIODIC_INSTANCE; module receipt only; no individual named audit located |
| S10-05 | `QuasiFeffermanB.LH_RESTART_OF_TAIL_ENERGY` | `Material/_vendor/QuasiFeffermanB/TailEnergy.lean`:202–219 | PERIODIC_INSTANCE; module receipt only; no individual named audit located |
| S10-06 | `QuasiFeffermanB.LH_UNIQUE_FUTURE_OF_REFERENCE_SHIFT_SERRIN` | `Material/_vendor/QuasiFeffermanB/TailUniqueness.lean`:87–131 | PERIODIC_INSTANCE; module receipt only; no individual named audit located |
| S10-07 | `QuasiFeffermanB.positive_reference_strict_shift_serrin` | `Material/_vendor/QuasiFeffermanB/TailUniqueness.lean`:60–85 | PERIODIC_INSTANCE; literal named retained type/axiom audit |
| S10-08 | `QuasiFeffermanB.LH_UNIQUE_FUTURE_OF_SMOOTH_REFERENCE` | `Material/_vendor/QuasiFeffermanB/TailUniqueness.lean`:149–158 | PERIODIC_INSTANCE; literal named retained type/axiom audit |
| S10-09 | `QuasiFeffermanB.Quasi_Fefferman_B_of_analytic_endpoints` | `Material/_vendor/QuasiFeffermanB/RootAssembly.lean`:63–76 | PERIODIC_CONDITIONAL_COMPOSITION; module receipt only; no individual named audit located |
| S10-10 | `QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED` | `Material/_vendor/QuasiFeffermanB/Endpoints/Root.lean`:15–16 | PERIODIC_ACCEPTED_ROOT; literal named retained type/axiom audit |
| S07-Q01 | `QFA.Energy.envelope_product_integral` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Energy/ProductBudget.lean`:90–125 | DOMAIN_NEUTRAL_EXACT; literal named retained type/axiom audit |
| S07-Q02 | `QFA.Energy.product_budget` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Energy/ProductBudget.lean`:191–212 | DOMAIN_NEUTRAL_EXACT; literal named retained type/axiom audit |
| S07-Q03 | `QFA.Energy.product_budget_Ioo` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Energy/ProductBudget.lean`:217–233 | DOMAIN_NEUTRAL_EXACT; literal named retained type/axiom audit |
| S07-Q04 | `QFA.Representation.EnergyProfile.energy_product_budget_Ioo` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Representation/EnergyProfile.lean`:164–183 | R3_NORM_PROFILE_EXACT_CONDITIONAL_ON_ENERGY_PROFILE; literal named retained type/axiom audit |
| S08-Q01 | `QFA.Endpoints.GoodTime.exists_good_time_of_integral_lt` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/GoodTime/Basic.lean`:38–65 | DOMAIN_NEUTRAL_EXACT; literal named retained type/axiom audit |
| S08-Q02 | `QFA.Endpoints.GoodTime.exists_subcritical_product_good_time` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/GoodTime/Cutoff.lean`:57–75 | DOMAIN_NEUTRAL_OLD_CONSTANT_WRAPPER; literal named retained type/axiom audit |
| S08-Q03 | `QFA.Endpoints.Composition.exists_subcritical_good_time_of_envelope` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Composition/GoodTimeOfEnvelope.lean`:30–50 | DOMAIN_NEUTRAL_OLD_CONSTANT_COMPOSITION; literal named retained type/axiom audit |
| S08-Q04 | `QFA.Representation.EnergyProfile.exists_subcritical_good_time` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Representation/EnergyProfile.lean`:189–212 | R3_NORM_PROFILE_OLD_CONSTANT_WRAPPER; literal named retained type/axiom audit |
| S08-Q05 | `QFA.Endpoints.Composition.exists_subcritical_good_time_with_strong_trace` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Composition/GoodTimeAndTrace.lean`:32–73 | R3_NORM_PROFILE_TRACE_OLD_CONSTANT_WRAPPER; literal named retained type/axiom audit |
| S10-Q01 | `QFA.Endpoints.Restart.strong_tendsto_of_inner_and_norm_bound` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Restart/HilbertTrace.lean`:50–75 | DOMAIN_NEUTRAL_EXACT; literal named retained type/axiom audit |
| S10-Q02 | `QFA.Endpoints.Restart.strong_right_trace_of_energy_start` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Restart/HilbertTrace.lean`:80–99 | DOMAIN_NEUTRAL_EXACT; literal named retained type/axiom audit |
| S10-Q03 | `QFA.Endpoints.Restart.shifted_strong_trace_of_energy_start` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Restart/HilbertTrace.lean`:103–116 | DOMAIN_NEUTRAL_EXACT; literal named retained type/axiom audit |
| S10-Q04 | `QFA.Endpoints.Restart.timeTranslate_memLp_Ioc` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Restart/TimeTranslate.lean`:84–94 | DOMAIN_NEUTRAL_EXACT; literal named retained type/axiom audit |
| S10-Q05 | `QFA.Endpoints.Restart.timeTranslate_ae_Ioc` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Restart/TimeTranslate.lean`:98–113 | DOMAIN_NEUTRAL_EXACT; literal named retained type/axiom audit |
| S10-Q06 | `QFA.Endpoints.Restart.timeTranslate_intervalIntegral` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Restart/TimeTranslate.lean`:118–122 | DOMAIN_NEUTRAL_EXACT; literal named retained type/axiom audit |
| S10-Q07 | `QFA.Endpoints.Restart.timeTranslate_intervalIntegrable` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Restart/TimeTranslate.lean`:125–132 | DOMAIN_NEUTRAL_EXACT; literal named retained type/axiom audit |
| S10-Q08 | `QFA.Assembly.Restart.energyProfile_timeTranslate` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/Restart.lean`:124–144 | R3_NORM_PROFILE_EXACT_CONDITIONAL_ON_ENERGY_START; literal named retained type/axiom audit |
| S10-Q09 | `QFA.Assembly.Restart.restartData_of_energyStart` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/Restart.lean`:149–164 | R3_NORM_PROFILE_EXACT_CONDITIONAL_ON_ENERGY_START; literal named retained type/axiom audit |
| S10-Q10 | `QFA.Assembly.Comparison.eq_on_Icc_of_ae_relative_energy` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/Comparison.lean`:85–108 | DOMAIN_NEUTRAL_EXACT_CONDITIONAL_COMPARISON; literal named retained type/axiom audit |
| S10-Q11 | `QFA.Assembly.TailComparison.ComparableOnNonnegative.eq_on_tail` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/TailComparison.lean`:142–150 | DOMAIN_NEUTRAL_EXACT_CONDITIONAL_COMPARISON; literal named retained type/axiom audit |
| S10-Q12 | `QFA.Assembly.TailComparison.restricted_restart_class_eq_singleton` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/TailComparison.lean`:172–184 | DOMAIN_NEUTRAL_EXACT_CONDITIONAL_COMPOSITION; literal named retained type/axiom audit |
| S10-Q13 | `QFA.Assembly.Chain.exists_selected_reference_and_tail_singleton` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/Chain.lean`:81–118 | R3_CARRIER_CONDITIONAL_OLD_CONSTANT_ASSEMBLY; literal named retained type/axiom audit |
| S10-Q14 | `QFA.Assembly.Chain.quantified_tail_assembly` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/Chain.lean`:165–196 | R3_CARRIER_CONDITIONAL_OLD_CONSTANT_ASSEMBLY; literal named retained type/axiom audit |
| S10-Q15 | `QFA.Assembly.Integrated.quantified_tail_assembly_of_analytic_inputs` | `Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/Integrated.lean`:99–122 | R3_CARRIER_CONDITIONAL_OLD_ANALYTIC_ROUTE; literal named retained type/axiom audit |
| S09-Q01 | `QFA.CorrectedPhysicalRoot.selectedTail_smooth` | `Quasi-Fefferman-A/CorrectedPhysicalRoot/QFACorrectedRoot/PhysicalRoot.lean`:93–109 | CONDITIONAL_SEMANTIC_TRANSPORT; named summary only; no full type transcript |
| S10-Q16 | `QFA.CorrectedPhysicalRoot.QUASI_FEFFERMAN_A_CORRECTED` | `Quasi-Fefferman-A/CorrectedPhysicalRoot/QFACorrectedRoot/PhysicalRoot.lean`:131–158 | CONDITIONAL_PHYSICAL_ROOT_INTERFACE_OLD_CONSTANTS; named summary only; no full type transcript |

## Hypotheses and boundaries

### S07-01: `QuasiFeffermanB.LH_ENERGY_BOUNDS`

Import: `QuasiFeffermanB.LHEnergy`.

Pointwise E<=E0 and integrable dissipation with integral Y<=E0/(2nu).

Does not establish the sharper weighted integral E*Y<=E0^2/(4nu).

### S07-02: `QuasiFeffermanB.criticalFourthPower_budget`

Import: `QuasiFeffermanB.CriticalTimeBudget`.

Arbitrary measure space, integrable gradient, measurable critical^2, nonnegative gradient, kinetic<=M, critical^2<=kinetic*gradient and integral gradient<=M/(2mu) imply integral critical^2<=M^2/(2mu).

Freezes kinetic at M; the denominator is 2mu, not the desired 4nu. Do not relabel it as the weighted-energy theorem.

### S07-03: `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`

Import: `Mathlib.MeasureTheory.Function.AbsolutelyContinuous`.

An interval-integrable real function has an absolutely continuous primitive from any basepoint in the interval.

Supplies AC of F(t)=integral_0^t Y, not by itself the energy majorant comparison.

### S07-04: `IntervalIntegrable.ae_hasDerivAt_integral`

Import: `Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm`.

For interval-integrable Banach-valued f, primitive derivative equals f almost everywhere in the interval, for all basepoints there.

Derivative is only a.e.; this is sufficient with the AC theorem, and does not require continuity of Y.

Inherited context: E is a complete real normed space; f: Real -> E.

### S07-05: `AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub`

Import: `Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun`.

For real absolutely continuous f and g, the integral of deriv f*g+f*deriv g is the endpoint product difference.

The recovered QFA.Energy.envelope_product_integral implements the AC product route using this declaration; see S07-Q01. This Mathlib dependency itself has no separately collected named audit in the periodic material receipt.

### S07-06: `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul`

Import: `Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun`.

Integration by parts for two real absolutely continuous functions.

Alternative to S07-05; requires actual AC hypotheses, not mere continuity or a.e. differentiability alone.

### S07-07: `IntervalIntegrable.continuousOn_mul`

Import: `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`.

Interval-integrable f multiplied on the left by continuous g on uIcc remains interval-integrable.

Use with f=Y and g=A or F; integrability of E*Y still needs measurable domination.

Inherited context: A is a normed ring, mu is a measure on Real; relevant instance A=Real and mu=volume.

### S07-08: `intervalIntegral.integral_mono_ae_restrict`

Import: `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`.

Compare integrals on a<=b from interval integrability of both functions and an a.e. order on restricted Icc.

The preceding section binders hab, hf and hg are actual theorem hypotheses and must be supplied.

Inherited context: Inherited binders at lines 1421-1422: hab : a <= b; hf : IntervalIntegrable f mu a b; hg : IntervalIntegrable g mu a b; f,g : Real -> Real.

### S07-09: `SingularClosure.CRITICAL_SQUARE_BUDGET_DIV`

Import: `SingularClosure.CriticalInvariant`.

Generic differential square-budget theorem with terminal remainder and denominator 4*(nu-C*a0).

Requires continuous A and X, a derivative at every time in Ico, a pointwise differential inequality and interpolation. These hypotheses are not supplied for a general LH energy path or an L1-dissipation primitive. It is not the requested weighted LH lemma.

### S08-01: `QuasiFeffermanB.exists_good_time_of_integral_lt`

Import: `QuasiFeffermanB.GoodTime`.

Arbitrary real f and predicate Good; T>0, c>=0, integrability on Ioo(0,T), a.e. Good, and integral f<c*T imply 0<t<T, Good t and f(t)<c.

Set f=E*Y, c=theta and T=tauA after proving the weighted bound and integrability. This theorem selects a witness but does not state the quantitative half-measure lower bound.

Inherited context: criticalTimeMeasure T is volume.restrict (Ioo 0 T), defined in CriticalTimeBudget.lean:20-21.

### S08-02: `MeasureTheory.mul_meas_ge_le_integral_of_nonneg`

Import: `Mathlib.MeasureTheory.Integral.Bochner.Basic`.

For a.e. nonnegative integrable real f, epsilon * mu.real{epsilon<=f} <= integral f.

For the half-measure claim use the finite measure volume.restrict(Ioo 0 tauA), positive theta, and integral E*Y<=theta*tauA/2.

Inherited context: Ambient measurable space alpha with measure mu; mu.real is real-valued measure.

### S08-03: `MeasureTheory.measure_sdiff`

Import: `Mathlib.MeasureTheory.Measure.MeasureSpace`.

Measure of s1 minus s2 is measure s1 minus measure s2 when s2 is a null-measurable subset of finite measure.

Useful for turning the bad-set Markov bound into the half-measure good set; finite interval and null measurability must be supplied.

Inherited context: Ambient measure mu and sets s1,s2.

### S08-04: `QuasiFeffermanB.LH_RESTART_AE_Ioo`

Import: `QuasiFeffermanB.LHRestart`.

From native periodic CriticalLerayHopf and nu>=0, a.e. s in Ioo(0,T) is H1 and its translated path is LH from the exact L2 trace.

Provides the exact periodic full-measure predicate pattern; R3 requires its own actual LH restart theorem.

### S08-05: `QuasiFeffermanB.LH_GOOD_SUBCRITICAL_TIME`

Import: `QuasiFeffermanB.GoodTime`.

Periodic LH path, strict periodic cutoff and a.e. Good yield H1 at a good time and small extended Fourier half-energy.

Uses periodic half-energy admission and 8*pi^2 cutoff; not the R3 E*Y threshold. Its proof calls the reusable S08-01 selector.

### S08-06: `QuasiFeffermanB.ZERO_LH_VELOCITY`

Import: `QuasiFeffermanB.ZeroData`.

Zero datum and nu>=0 force SameVelocity with zero at every nonnegative time, via nonnegative energy and the L2 representative.

Replace the periodic carrier/measure by actual whole-space L2; preserve spatial-a.e. equality at every time, not pointwise equality of arbitrary representatives.

### S09-01: `QuasiFeffermanB.HAS_SMOOTH_TAIL_OF_POSITIVE_REFERENCE`

Import: `QuasiFeffermanB.TailRegularity`.

A positive-time smooth periodic reference, 0<=s<delta and spatial-a.e. identification after s yield a closed classical tail from delta.

Closed QFA cutoff is available once s<tauA; actual whole-space reference and PDE translation are still required.

### S09-02: `QuasiFeffermanB.physicalH1_gradient_eq_smooth`

Import: `QuasiFeffermanB.TailEnergy`.

A native physical H1 weak gradient agrees a.e. with the smooth periodic derivative if velocity representatives agree a.e.

Proof uses periodic smooth H1 approximants and integration by parts. R3 must supply weak-gradient uniqueness/density in its own Sobolev space.

### S09-03: `QuasiFeffermanB.physicalH1_gradientEnergy_eq_smooth`

Import: `QuasiFeffermanB.TailEnergy`.

Converts weak-gradient energy to physical smooth dissipation after spatial-a.e. velocity identification.

Use a.e. in time when integrating a weak gradient; do not assert an arbitrary chosen G(delta) is the correct derivative at the isolated tail start.

### S09-04: `SingularClosure.CRITICAL_SMOOTH_NSE_ENERGY_IDENTITY`

Import: `SingularClosure.CriticalSmoothEnergy`.

Actual positive-time smooth periodic NSE gives dissipation integrability and exact energy equality on each positive closed slab.

The proof derives spatial integrability/continuity using the compact cube and periodic cancellation. R3 needs energy-class control and justified whole-space integration by parts.

Inherited context: Inherited Classical binders lines 166-175: nu, velocity u, pressure p; hu : CriticalPositiveSolenoidalTest u; hp : positive-time spatial pressure smoothness; hpp : pressure periodicity; hNSE : actual NSE equation.

### S09-05: `intervalIntegral.integral_congr_ae_restrict`

Import: `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`.

Equality a.e. on the unoriented interval restriction gives equality of interval integrals.

Direct utility for transferring weak-gradient dissipation to the strong representative.

Inherited context: Relevant instance real-valued integrands, volume measure.

### S09-06: `intervalIntegral.integral_comp_sub_right`

Import: `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`.

Translation formula for an interval integral of f(x-d).

Direct time-coordinate identity; does not supply NSE or weak-gradient identification.

Inherited context: Inherited f : Real -> E with real normed-space structure; interval endpoints a,b.

### S09-07: `QuasiFeffermanB.LH_TAIL_ENERGY_OF_POSITIVE_REFERENCE`

Import: `QuasiFeffermanB.TailEnergy`.

nu>0, periodic LH path, positive-time smooth reference, 0<=s<delta and agreement at every time r>s imply tail energy equality.

Proof uses a.e.-in-time H1, weak-gradient uniqueness, periodic smooth energy identity and time translation. This is the correct assembly pattern, not an R3 theorem.

### S10-01: `QuasiFeffermanB.strong_tendsto_of_inner_and_norm_bound`

Import: `QuasiFeffermanB.LHRestart`.

In any real inner-product space, convergence of inner(f_i,a) to norm(a)^2 and eventual norm(f_i)^2<=norm(a)^2 imply strong convergence to a.

Directly reusable with whole-space L2. A weak-continuity/energy argument must provide its two hypotheses.

### S10-02: `QuasiFeffermanB.timeTranslate_memLp_Ioc`

Import: `QuasiFeffermanB.TimeTranslate`.

For any normed additive group and exponent p, an Lp path on Ioc(0,T+s) remains Lp on Ioc(0,T) after nonnegative translation s.

No spatial domain assumption; useful for R3 energy and Serrin time classes.

### S10-03: `QuasiFeffermanB.timeTranslate_ae_Ioc`

Import: `QuasiFeffermanB.TimeTranslate`.

Transports arbitrary a.e. time predicates through a nonnegative time translation.

No periodic hypothesis in the exact type; actual PDE restart is separate.

### S10-04: `QuasiFeffermanB.LH_RESTART_FROM_ENERGY_START`

Import: `QuasiFeffermanB.LHRestart`.

A periodic LH path plus an energy inequality from a specified nonnegative start gives translated LH membership at its exact trace.

Reconstructs momentum, energy spaces, weak/strong trace and interval energy fields; R3 must prove those actual translated properties.

### S10-05: `QuasiFeffermanB.LH_RESTART_OF_TAIL_ENERGY`

Import: `QuasiFeffermanB.TailEnergy`.

A tail energy equality at delta>=0 gives translated LH membership from u(delta).

Does not demand H1 correctness of the arbitrary weak-gradient representative at delta; requires the actual R3 analogue of restart.

### S10-06: `QuasiFeffermanB.LH_UNIQUE_FUTURE_OF_REFERENCE_SHIFT_SERRIN`

Import: `QuasiFeffermanB.TailUniqueness`.

Periodic LH path identified with a positive smooth reference after s, s<delta, and a finite-horizon shifted L4_t L6_x Serrin condition imply UniqueFuture.

Explicit Serrin variant is the more transparent port target: R3 must derive this norm control from its actual H1 strong tail and whole-space Sobolev, then supply whole-space weak-strong comparison.

### S10-07: `QuasiFeffermanB.positive_reference_strict_shift_serrin`

Import: `QuasiFeffermanB.TailUniqueness`.

A strictly positive shift of PositiveSmoothNSE is in finite-horizon L4_t L6_x.

Proof uses continuity of the periodic spatial L6 norm and compactness. Pointwise smoothness alone on noncompact R3 does not supply the same conclusion.

### S10-08: `QuasiFeffermanB.LH_UNIQUE_FUTURE_OF_SMOOTH_REFERENCE`

Import: `QuasiFeffermanB.TailUniqueness`.

A periodic LH path agrees after s with a positive smooth reference; at every delta>s it has a unique future from its own trace.

Its discharged Serrin premise relies on S10-07. Preserve finite-horizon H1/L6 control when constructing an R3 counterpart.

### S10-09: `QuasiFeffermanB.Quasi_Fefferman_B_of_analytic_endpoints`

Import: `QuasiFeffermanB.RootAssembly`.

Periodic global LH existence and ExactH1Admission for each positive viscosity imply the frozen QFB root.

hexists and hadmit are actual premises in this theorem. An analogous QFA assembly is conditional until its whole-space instances are proved; a standard-only axiom report would not erase these parameters.

### S10-10: `QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED`

Import: `QuasiFeffermanB.Endpoints.Root`.

Closed periodic QFB theorem, assembled through Quasi_Fefferman_B_of_LH_existence Q01_LERAY_HOPF_EXISTENCE; TailChain discharges ExactH1Admission.

This exact name has a literal cached type/axiom report. It is the accepted periodic reference, not a whole-space root.

### S07-Q01: `QFA.Energy.envelope_product_integral`

Import: `QFA.Endpoints.Energy.ProductBudget`.

For interval-integrable D and nonzero nu, proves integral envelope*D=(M^4-envelope(R)^2)/(4nu) by AC product FTC and a.e. derivative substitution.

No PDE hypothesis and no derivative/continuity assumption on the weak energy E; this is the actual implemented identity.

### S07-Q02: `QFA.Energy.product_budget`

Import: `QFA.Endpoints.Energy.ProductBudget`.

For R>=0,nu>0, interval-integrable D, a.e. measurable E, nonnegative E,D and E<=M^2-2nu*integral D a.e., derives ED integrability, residual-square bound and integral ED<=M^4/(4nu).

Set M=||a||2, not E0. The physical LH path must supply the profile facts; the theorem proves the envelope identity internally.

### S07-Q03: `QFA.Energy.product_budget_Ioo`

Import: `QFA.Endpoints.Energy.ProductBudget`.

Same hypotheses as product_budget; conclusion uses literal volume.restrict(Ioo 0 R) integrability and open-set integral ED<=M^4/(4nu).

Direct scalar interface for current good-time selector; no NSE membership is inferred.

### S07-Q04: `QFA.Representation.EnergyProfile.energy_product_budget_Ioo`

Import: `QFA.Endpoints.Representation.EnergyProfile`.

EnergyProfile on actual full-volume L2(R3;R3), nu>0 and R>0 supplies product integrability and integral velocityEnergy*gradientEnergy<=||a||^4/(4nu).

EnergyProfile69-82 contains finite-horizon measurability, coordinate time-L2 gradients, zero-start energy. It does not identify G as the physical weak gradient or u as an LH solution.

Inherited context: RealSpatialL2=Lp (EuclideanSpace Real (Fin 3)) 2 full spatial volume (lines42-44); EnergyProfile fields69-82. G supplies three L2 fields without a weak-derivative predicate.

### S08-Q01: `QFA.Endpoints.GoodTime.exists_good_time_of_integral_lt`

Import: `QFA.Endpoints.GoodTime.Basic`.

Arbitrary f and Good: positive T, nonnegative c, integrable f, a.e. Good and integral f<c*T give 0<s<T,Good(s),f(s)<c.

Use with current theta,tauA after the nonzero branch. This conclusion selects a witness, not the quantitative half-measure set.

### S08-Q02: `QFA.Endpoints.GoodTime.exists_subcritical_product_good_time`

Import: `QFA.Endpoints.GoodTime.Cutoff`.

Combines ED budget with strict delta>M^4/(16*pi^2*nu^5) to select ED(s)<4*pi^2*nu^4 and retain Good.

Historical threshold/cutoff differ from current Sobolev theta=nu^4/S6^6 and safe tauA; do not claim current numeric endpoint from this wrapper.

### S08-Q03: `QFA.Endpoints.Composition.exists_subcritical_good_time_of_envelope`

Import: `QFA.Endpoints.Composition.GoodTimeOfEnvelope`.

Derives the sharp product budget from the energy envelope and then selects a good time under the historical strict cutoff.

Its old threshold and strict cutoff are literal type parameters; adapt through generic S08-Q01 for current constants.

### S08-Q04: `QFA.Representation.EnergyProfile.exists_subcritical_good_time`

Import: `QFA.Endpoints.Representation.EnergyProfile`.

Actual full-volume L2 norm profile and a.e. Good yield the old subcritical product witness.

Does not supply actual weak-gradient identification, H1 admission or translated momentum.

Inherited context: RealSpatialL2=Lp (EuclideanSpace Real (Fin 3)) 2 full spatial volume (lines42-44); EnergyProfile fields69-82. G supplies three L2 fields without a weak-derivative predicate.

### S08-Q05: `QFA.Endpoints.Composition.exists_subcritical_good_time_with_strong_trace`

Import: `QFA.Endpoints.Composition.GoodTimeAndTrace`.

Adds weak pairing continuity and a.e. all-upper-endpoint energy starts; returns 0<s<delta,Good,small product,retained energy-start and strong right/translated traces.

Physical LH restart membership remains a separate theorem. Old threshold/cutoff; no positive-measure estimate stated.

### S10-Q01: `QFA.Endpoints.Restart.strong_tendsto_of_inner_and_norm_bound`

Import: `QFA.Endpoints.Restart.HilbertTrace`.

Any real inner-product space: pairing with a tends to ||a||^2 and eventual norm-square bound by ||a||^2 imply strong convergence to a.

No completeness or physical spatial structure needed; does not prove the norm bound itself.

### S10-Q02: `QFA.Endpoints.Restart.strong_right_trace_of_energy_start`

Import: `QFA.Endpoints.Restart.HilbertTrace`.

Any real inner-product space; nu,s>=0, nonnegative dissipation, selected-pairing continuity and energy start at all upper endpoints imply strong right trace at s.

Retains the energy-start premise; does not establish its almost-everywhere validity for actual NSE.

### S10-Q03: `QFA.Endpoints.Restart.shifted_strong_trace_of_energy_start`

Import: `QFA.Endpoints.Restart.HilbertTrace`.

Translates the preceding strong right trace into the exact zero-start trace of timeTranslate s u.

Physical weak momentum and actual LH membership are not conclusions.

### S10-Q04: `QFA.Endpoints.Restart.timeTranslate_memLp_Ioc`

Import: `QFA.Endpoints.Restart.TimeTranslate`.

For any normed additive group and s>=0, transports a supplied MemLp class on Ioc(0,T+s) to the shifted class on Ioc(0,T).

This is measure transport, not a spatial Sobolev or regularity theorem.

### S10-Q05: `QFA.Endpoints.Restart.timeTranslate_ae_Ioc`

Import: `QFA.Endpoints.Restart.TimeTranslate`.

Transports an arbitrary a.e. predicate under nonnegative time shift with exact restricted measures.

A.e. transported facts remain a.e.; this does not improve arbitrary point values.

### S10-Q06: `QFA.Endpoints.Restart.timeTranslate_intervalIntegral`

Import: `QFA.Endpoints.Restart.TimeTranslate`.

Exact scalar translated interval-integral identity on arbitrary endpoints.

Totalized integral identity; supply actual integrability separately for analytic use.

### S10-Q07: `QFA.Endpoints.Restart.timeTranslate_intervalIntegrable`

Import: `QFA.Endpoints.Restart.TimeTranslate`.

Transports genuine interval integrability from shifted endpoints to the translated scalar integrand.

Use alongside the integral identity, not as a substitute for spatial energy estimates.

### S10-Q08: `QFA.Assembly.Restart.energyProfile_timeTranslate`

Import: `QFA.Assembly.Restart`.

An EnergyProfile and nonnegative valid energy start yield the translated EnergyProfile at datum u(s).

Profile has no weak-gradient relation, divergence or momentum field; those are still required for actual LH restart.

### S10-Q09: `QFA.Assembly.Restart.restartData_of_energyStart`

Import: `QFA.Assembly.Restart`.

Combines translated profile, weak pairing continuity and strong initial trace into RestartData.

RestartData has exactly these three fields and is not physical solution-class membership.

### S10-Q10: `QFA.Assembly.Comparison.eq_on_Icc_of_ae_relative_energy`

Import: `QFA.Assembly.Comparison`.

Finite normed-carrier comparison from continuous/nonnegative/integrable coefficient, integrable relative-energy product, a.e. good starts, same strong trace, initial values and relative-energy inequality at every upper endpoint.

Actual NSE cross-testing/relative-energy estimate must be supplied. The initial values are separate from right traces and are needed to include zero.

### S10-Q11: `QFA.Assembly.TailComparison.ComparableOnNonnegative.eq_on_tail`

Import: `QFA.Assembly.TailComparison`.

Comparison of the shifted source with v implies u(t)=v(t-s) for every t>=s in the normed carrier.

In L2 this is equality of equivalence classes, not equality of arbitrary pointwise representatives.

Inherited context: TailComparison.lean38: variable {V : Type*} [NormedAddCommGroup V]; ComparableOnNonnegative is finite-horizon ComparisonData at every positive T (lines43-66).

### S10-Q12: `QFA.Assembly.TailComparison.restricted_restart_class_eq_singleton`

Import: `QFA.Assembly.TailComparison`.

After s<delta, source comparison, actual admission of the shifted reference at u(delta), and new comparison for every member give the exact restricted singleton.

Actual membership is an independent premise; nonnegative-time equality cannot imply membership of different negative-time extensions.

Inherited context: TailComparison.lean38: variable {V : Type*} [NormedAddCommGroup V]; ComparableOnNonnegative is finite-horizon ComparisonData at every positive T (lines43-66).

### S10-Q13: `QFA.Assembly.Chain.exists_selected_reference_and_tail_singleton`

Import: `QFA.Assembly.Chain`.

Combines energy profile, a.e. energy starts, actual restart admission, subcritical reference witness and ReferencePorts to yield a selected reference and exact-trace future singleton.

Admissible,Reference,Good are parameters; hRestart,hReference,hPorts remain analytic inputs. Historical cutoff/threshold.

### S10-Q14: `QFA.Assembly.Chain.quantified_tail_assembly`

Import: `QFA.Assembly.Chain`.

Quantifies the preceding chain using ClassRealization, SubcriticalReferenceConstruction and ReferencePorts.

Nonemptiness, actual class/restart interpretation, global strong reference and comparison remain explicit premises; no literal physical QFA root.

### S10-Q15: `QFA.Assembly.Integrated.quantified_tail_assembly_of_analytic_inputs`

Import: `QFA.Assembly.Integrated`.

Derives pointwise absorption from spectral/Agmon/extension inputs and invokes the explicit ReferenceConstructionFromAbsorption backend plus class and reference ports.

The local-strong evolution/temporal invariant/continuation backend is not constructed here. Current elementary Sobolev route need not adopt the historical Agmon inputs.

### S09-Q01: `QFA.CorrectedPhysicalRoot.selectedTail_smooth`

Import: `QFACorrectedRoot.PhysicalRoot`.

Uses s<delta to get positive reference time delta-s, then transfers supplied SmoothNSETail across the already established tail equality.

SmoothNSETail is an arbitrary predicate and SmoothReferencePorts are assumed; no actual R3 pressure, smooth solution or tail energy identity is derived.

Inherited context: QFARoot47-59 quantifies arbitrary Domain/Admissible/SmoothNSETail and requires delta>norm(a)^4/(16*pi^2*nu^5). SmoothReferencePorts62-73 contains assumed positive_time and transport.

### S10-Q16: `QFA.CorrectedPhysicalRoot.QUASI_FEFFERMAN_A_CORRECTED`

Import: `QFACorrectedRoot.PhysicalRoot`.

Assembles QFARoot from class realization, reference ports, spectral/Agmon inputs, corrected reference backend and smooth semantic ports.

Retained evidence is a summary, without the full exact type/axiom log; source type is conditional and uses historical strict cutoff. Not current QFA acceptance.

Inherited context: QFARoot47-59 quantifies arbitrary Domain/Admissible/SmoothNSETail and requires delta>norm(a)^4/(16*pi^2*nu^5). SmoothReferencePorts62-73 contains assumed positive_time and transport.

## Passive external-audit names

No audit commands were executed. The companion JSON lists every exact import/name and separates package roots. For a future authorized matching external environment, the passive request for each listed name is:

```lean
#check @FULL_NAME
#print axioms FULL_NAME
```

This is an audit request format, not compiler evidence. Existing retained receipts and logs are recorded independently above.

## Review counts

58 anchors total; 26 recovered-QFA additions, of which 24 have matching retained full named types/axiom logs and 2 have summary evidence only. Local Lean/Lake/kernel executions: 0. New A-tier results: 0.
