# Source anchors for checklist steps 3–6

## Conclusion

The periodic implementation contains actual PDE existence, restart, weak–strong comparison and small-data reference theorems with cached exact declaration audits. The recovered QFA branch contains reusable full-volume L2 trace/translation proofs, every-time Grönwall comparison, pointwise absorption and a conditional root assembly. It still assumes the physical whole-space weak solution realization, the relative-energy comparison input and the local-evolution/temporal-bootstrap/continuation backend. None of those ports is removed by a clean axiom list.

## Pinned sources

| Source | Immutable revision | Toolchain / role |
|---|---|---|
| native | `fdb515d8bde35ec8021bbc26f360aca8dfa2855c` | leanprover/lean4:v4.33.0; randogelist/Methboke |
| methlib_vendor | `96033dd69c994bec337a87369a6c27256e724980` | leanprover/lean4:v4.33.0; randogelist/Methlib |
| qfa | `53b2318c2b586137b6db74c4d3a41bb0b964b2d8` | leanprover/lean4:v4.33.0; randogelist/Methlib |
| upstream | `f9e8bc5b38b6e212696e8a30e3e91517af887bbd` | leanprover/lean4:v4.34.0-rc2; openai/NavierStokesAndEuler |
| mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` | Pinned dependency; leanprover-community/mathlib4 |

QFA source snapshot: `/workspace/scratch/9d4dc6f7f47a/anchor_sources/methlib-53b2318c2b586137b6db74c4d3a41bb0b964b2d8`. Native source: `/workspace/scratch/9d4dc6f7f47a/Methboke-AC-Integration/Material`. All principal native files in the anchors below were compared byte-for-byte to the staged fdb snapshot; each match is recorded in JSON. All 269 vendored manifest source files matched Methlib96033 and listed SHA256. Upstream uses a separate 4.34-rc2/85e3 dependency context, so its declarations are source reuse candidates here.

## Checklist assessment

| Step | Strongest reusable work | Exact remaining whole-space edge |
|---|---|---|
| 3. Actual local H1 NSE existence and continuation | Native periodic smooth-data existence with H1-controlled lifespan; actual maximal continuation and enstrophy-square criterion. QFA explicitly identifies reference-construction port. | Whole-space arbitrary H1 local strong construction, its actual PDE/trace estimates and maximal continuation; cannot instantiate from periodic or compact candidate wrappers. |
| 4. Global Leray–Hopf existence and exact restarts | Periodic global LH construction and full a.e. LH restart; QFA full-volume L2 time-translation and strong right-trace proof. | Actual R3 weak momentum/divergence/weak-gradient solution class and nonemptiness, energy profile realization, translated full LH membership. These remain ClassRealization fields. |
| 5. Weak–strong uniqueness from common restart trace | Actual periodic weak–strong finite-window comparison; generic QFA all-time normed comparison from explicit scalar premises; upstream actual R3 H3/compact-smooth comparison. | Derive ComparisonData from actual R3 LH and strong equations with required coefficient/product integrability. Existing upstream competitor assumptions are stronger than LH. |
| 6. Small energy–enstrophy product bootstrap and global strong restart | Periodic numerical H-half smallness admits global actual reference; native actual periodic enstrophy derivative/continuation; QFA scalar/full-L2 pointwise absorption under explicit analytic endpoints. | Actual R3 energy/enstrophy evolution, preservation of strict product smallness and uniform margin along lifespan, integrated dissipation/continuation, construction of reference from selected H1 datum. Historical threshold/cutoff differs target. |

## Step 3: Actual local H1 NSE existence and continuation

### P3_LOCAL — `MethbokeAddon.WeakFouriermanB.local_initial_classical_front_exists; uniform_H1_local_initial_classical_front_exists`

**Scope:** ACTUAL_PERIODIC_PDE. [Source, lines 24–58](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/MethbokeAddon/WeakFouriermanB/LocalExistence.lean#L24-L58).

**Hypotheses:** ν>0; R≥0; SmoothSigmaZero a (smooth, periodic, solenoidal, mean zero); physical dissipation or H1-square ≤R.

**Conclusion and proof:** A positive uniform lifespan and actual InitialClassicalFront velocity/normalized pressure, including t=0. Uniform finite Galerkin estimates → untruncated local Sobolev flow → physical PDE recovery. No assumed local-existence port; datum is still smooth, not arbitrary rough H1.

### P3_FRONT — `MethbokeAddon.WeakFouriermanB.InitialClassicalFront`

**Scope:** DEFINITION_OF_ACTUAL_PERIODIC_PDE. [Source, lines 29–49](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/MethbokeAddon/WeakFouriermanB/FiniteCapGluing.lean#L29-L49).

**Hypotheses:** Structure fields: smooth on [0,T)×R3, periodic velocity/pressure, divergence free, actual NSE, initial equality, velocity and pressure mean zero.

**Conclusion and proof:** Exact semantic output of the existence theorem. Read all fields; a class definition itself is not existence.

### P3_CONTINUE — `MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_eq_top_of_uniform_H1`

**Scope:** ACTUAL_PERIODIC_PDE. [Source, lines 42–83](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/MethbokeAddon/WeakFouriermanB/StrongContinuation.lean#L42-L83).

**Hypotheses:** ν>0; actual MaximalClassicalFront; one R bounds physicalH1Square for every nonnegative time before Tmax.

**Conclusion and proof:** Tmax=∞. Choose restart near a hypothetical finite endpoint; smooth slice + uniform local existence + exact finite gluing contradict maximality.

### P3_SQUARE — `MethbokeAddon.WeakFouriermanB.initial_front_extends_of_dissipation_square; maximal_classical_front_no_finite_dissipation_square`

**Scope:** ACTUAL_PERIODIC_PDE. [Source, lines 30–73](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/MethbokeAddon/WeakFouriermanB/PhysicalEndpointContinuation.lean#L30-L73).

**Hypotheses:** ν,T>0; actual classical front; Integrable (physicalDissipation(u t)^2) on (0,T).

**Conclusion and proof:** A strictly longer actual front preserving old velocity and normalized pressure; impossible finite maximal lifespan with that whole-interval budget. Derive uniform H1 bound, construct restart and glue; no endpoint value or endpoint regularity assumed.

### Q4_CLASS — `QFA.Assembly.Chain.ClassRealization`

**Scope:** ASSUMED_PHYSICAL_REALIZATION_PORT. [Source, lines 124–143](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/Chain.lean#L124-L143).

**Hypotheses:** Arbitrary Domain, Admissible and Good predicates.

**Conclusion and proof:** nonempty, initial value/trace, energy profile/good starts, restart_admission are record fields. Root projects these fields. There is no constructor here proving physical R3 LH existence or full restart membership.

### Q6_BACKEND — `QFA.CorrectedPhysicalRoot.CorrectedReferenceConstructionFromAbsorption`

**Scope:** ASSUMED_LOCAL_EVOLUTION_AND_GLOBAL_CONTINUATION_PORT. [Source, lines 114–125](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/CorrectedPhysicalRoot/QFACorrectedRoot/Analytic.lean#L114-L125).

**Hypotheses:** A function from CorrectedPointwiseAbsorption ν to SubcriticalReferenceConstruction.

**Conclusion and proof:** Would return a global reference for a selected subcritical restart. Comment and type leave physical derivative realization, local strong evolution, temporal invariant and continuation explicit.

### Q6_REFERENCE — `QFA.Assembly.Chain.SubcriticalReferenceConstruction`

**Scope:** ASSUMED_REFERENCE_EXISTENCE_PORT. [Source, lines 148–157](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/Chain.lean#L148-L157).

**Hypotheses:** For every admitted trajectory and selected good start with energy start, RestartData and ED<4π²ν⁴.

**Conclusion and proof:** ∃v, Reference(u s)v. No inhabitant of this construction input was located in the inspected sources; this is the input used by tail assembly, not a theorem proving arbitrary H1 existence.

### U3_CLASS — `NavierStokesR3.H3Comparison.StrongSolutionOnIcc`

**Scope:** ACTUAL_R3_STRONG_SOLUTION_DEFINITION_ONLY. [Source, lines 30–46](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/H3StrongSolution.lean#L30-L46).

**Hypotheses:** H3 curve, actual L2 time derivative with HasDerivAt, C1 pressure, div-free weak jets, actual forced NSE.

**Conclusion and proof:** Defines a strong-solution class. No existence for arbitrary H1 data is supplied by the definition.

### U3_CANDIDATE — `NavierStokesR3.H3Comparison.strongSolution_of_compact_slab; candidate_classicalH3Solution`

**Scope:** R3_ADAPTER_FOR_ALREADY_SUPPLIED_SOLUTION. [Source, lines 87–126](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/H3CandidateStrong.lean#L87-L126).

**Hypotheses:** Already supplied smooth compact-support slab solving actual PDE; candidate variant requires CandidateProperties ν u p f K.

**Conclusion and proof:** StrongSolutionOnIcc / ClassicalH3Solution for that supplied candidate. Converts known compact classical field into H3 class; not an initial-value construction for arbitrary data.

### M3_ODE — `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`

**Scope:** GENERIC_BANACH_ODE_PRIMITIVE. [Source, lines 57–68](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/ODE/ExistUnique.lean#L57-L68).

**Hypotheses:** Complete normed space; IsPicardLindelof with bounded locally Lipschitz vector field, continuous time dependence and interval-size control; initial point in specified ball.

**Conclusion and proof:** Actual ODE solution on prescribed closed interval. General primitive only. No inspected instantiation realizes the unbounded whole-space NSE operator on H1.


## Step 4: Global Leray–Hopf existence and exact restarts

### P4_LH — `QuasiFeffermanB.Q01_LERAY_HOPF_EXISTENCE`

**Scope:** ACTUAL_PERIODIC_PDE. [Source, lines 35–149](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/_vendor/QuasiFeffermanB/Endpoints/LerayHopfExistence.lean#L35-L149).

**Hypotheses:** ν>0; a:CriticalPhysicalL2; EnergySigmaZero a.

**Conclusion and proof:** ∃u,G, CriticalLerayHopf ν a u G. Global Galerkin limit plus actual weak momentum, H1 realization, initial data, weak continuity, strong initial trace, and all energy fields. This is not merely finite-dimensional Galerkin existence.

### P4_CLASS — `SingularClosure.CriticalPhysicalL2; CriticalLerayHopf`

**Scope:** PERIODIC_CARRIER_AND_CLASS. [Source, lines 24–62](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/_vendor/SingularClosure/CriticalLerayHopf.lean#L24-L62).

**Hypotheses:** CriticalPhysicalL2 is Lp Vec 2 (volume.restrict unitCube); class includes actual periodic weak momentum, energy regularity and strong initial trace.

**Conclusion and proof:** 11-field periodic Leray–Hopf class. All class fields and measure restriction read. Full-space-looking Vec is used with unit-cube measure and periodic conditions; not R3 finite-energy LH.

### P4_TRACE — `QuasiFeffermanB.lh_strong_right_trace_of_energy_start`

**Scope:** ACTUAL_PERIODIC_TRACE. [Source, lines 117–149](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/_vendor/QuasiFeffermanB/LHRestart.lean#L117-L149).

**Hypotheses:** Existing CriticalLerayHopf; ν≥0; s≥0; energy inequality from s to every r≥s.

**Conclusion and proof:** Strong L2 right trace at exactly v(s). Weak continuity + norm bound → Hilbert strong convergence.

### P4_RESTART — `QuasiFeffermanB.LH_RESTART_FROM_ENERGY_START`

**Scope:** ACTUAL_PERIODIC_PDE. [Source, lines 215–276](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/_vendor/QuasiFeffermanB/LHRestart.lean#L215-L276).

**Hypotheses:** Existing CriticalLerayHopf; ν≥0; s≥0; all-upper-endpoint energy-start inequality.

**Conclusion and proof:** Translated velocity and gradient satisfy full CriticalLerayHopf with datum criticalL2Representative(v s). Reconstructs all class fields, including translated momentum and the derived strong trace.

### P4_RESTART_AE — `QuasiFeffermanB.LH_RESTART_AE; LH_RESTART_AE_Ioc; LH_RESTART_AE_Ioo`

**Scope:** ACTUAL_PERIODIC_PDE. [Source, lines 287–324](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/_vendor/QuasiFeffermanB/LHRestart.lean#L287-L324).

**Hypotheses:** Existing CriticalLerayHopf and ν≥0.

**Conclusion and proof:** Almost every positive start has actual physical H1 slice and full restarted LH membership, including every finite open observation interval. Good energy-start full-measure set plus previous restart theorem.

### Q4_TRACE — `QFA.Endpoints.Restart.strong_tendsto_of_inner_and_norm_bound; strong_right_trace_of_energy_start; shifted_strong_trace_of_energy_start`

**Scope:** REUSABLE_GENERIC_HILBERT_PROOF. [Source, lines 50–116](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Restart/HilbertTrace.lean#L50-L116).

**Hypotheses:** Any real inner-product space; weak pairing continuity on t≥0; ν,s≥0; nonnegative dissipation; all-endpoint energy-start inequality.

**Conclusion and proof:** Strong right trace at s and exact translated zero trace. Expands squared distance, uses norm upper bound and squeeze; then genuine time-filter translation. No completeness or periodic carrier needed.

### Q4_RESTART — `QFA.Assembly.Restart.energyProfile_timeTranslate; restartData_of_energyStart`

**Scope:** REUSABLE_ACTUAL_FULL_VOLUME_L2_PROFILE_PROOF. [Source, lines 124–163](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/Restart.lean#L124-L163).

**Hypotheses:** Actual full-volume L2 energy profile; ν,s≥0; weak pairing continuity; valid energy start.

**Conclusion and proof:** Shifted EnergyProfile + weak pairing continuity + strong shifted initial trace. Restricted measure-preserving time shift derives measurability/MemLp; energy-start inequality transports; Hilbert trace closes exact strong trace.

### Q4_RESTART_TYPE — `QFA.Assembly.Restart.EnergyStart; RestartData`

**Scope:** INTERFACE_WITH_NO_PDE_CLAIM. [Source, lines 47–64](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/Restart.lean#L47-L64).

**Hypotheses:** Supplied field trajectories in full-volume L2.

**Conclusion and proof:** Energy-start inequality and three derived restart fields. No momentum equation, gradient identification, divergence or LH membership occurs in RestartData.

### Q4_CLASS — `QFA.Assembly.Chain.ClassRealization`

**Scope:** ASSUMED_PHYSICAL_REALIZATION_PORT. [Source, lines 124–143](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/Chain.lean#L124-L143).

**Hypotheses:** Arbitrary Domain, Admissible and Good predicates.

**Conclusion and proof:** nonempty, initial value/trace, energy profile/good starts, restart_admission are record fields. Root projects these fields. There is no constructor here proving physical R3 LH existence or full restart membership.


## Step 5: Weak–strong uniqueness from common restart trace

### P5_SERRIN — `SingularClosure.CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON`

**Scope:** ACTUAL_PERIODIC_WEAK_STRONG. [Source, lines 37–173](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/_vendor/SingularClosure/CriticalSerrinUniqueness.lean#L37-L173).

**Hypotheses:** ν>0; LH competitor; positive smooth solenoidal periodic reference; actual reference PDE; common strong L2 initial trace; reference L4_t L6_x on (0,T].

**Conclusion and proof:** Every t∈(0,T] has spatial-a.e. equality. Derives relative-energy estimate from actual weak/strong equations and controls convection; selects admissible starts tending to zero and applies Grönwall.

### P5_FINITE — `MethbokeAddon.WeakFouriermanB.finite_window_leray_hopf_serrin_comparison`

**Scope:** ACTUAL_PERIODIC_WEAK_STRONG. [Source, lines 27–169](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/MethbokeAddon/WeakFouriermanB/FiniteWindowSerrinComparison.lean#L27-L169).

**Hypotheses:** Same LH/reference assumptions; actual reference PDE and pressure requirements only on (0,T]; finite L4L6 norm.

**Conclusion and proof:** Every-time spatial-a.e. equality in (0,T]. Finite-window relative-energy proof. The globally defined smooth test is not assumed to solve NSE after T.

### P5_MAXIMAL — `MethbokeAddon.WeakFouriermanB.maximal_front_leray_hopf_identification`

**Scope:** ACTUAL_PERIODIC_WEAK_STRONG. [Source, lines 27–46](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/MethbokeAddon/WeakFouriermanB/MaximalLerayHopfIdentification.lean#L27-L46).

**Hypotheses:** ν>0; SmoothSigmaZero datum; actual MaximalClassicalFront; any CriticalLerayHopf with same initial datum.

**Conclusion and proof:** Every nonnegative t<Tmax, including t=0, has spatial-a.e. equality with maximal front. Shorter smooth fronts supply finite-window Serrin bound; t=0 uses initial fields.

### Q5_GRONWALL — `QFA.Assembly.Comparison.eq_on_Ioc_of_ae_relative_energy; eq_on_Icc_of_ae_relative_energy`

**Scope:** REUSABLE_GENERIC_COMPARISON_PROOF. [Source, lines 40–108](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/Comparison.lean#L40-L108).

**Hypotheses:** Any normed additive group; nonnegative continuous finite-integrable coefficient; integrable coefficient×squared-difference; a.e. good starts; common strong trace; all-endpoint relative-energy inequality; initial values for closed interval.

**Conclusion and proof:** Equality at every positive time, and at zero when explicit initial values supplied. Constructs admissible times tending to zero from full-measure set and supplies actual finite integral as Grönwall budget. The PDE relative-energy inequality is not derived here.

### Q5_DATA — `QFA.Assembly.TailComparison.ComparisonData; ComparableOnNonnegative; ComparisonData.eq_on_Icc`

**Scope:** EXPLICIT_COMPARISON_PREMISE_AND_PROVED_CONSEQUENCE. [Source, lines 43–88](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/TailComparison.lean#L43-L88).

**Hypotheses:** ComparisonData requires coefficient/product integrability, good starts, both traces/values and relative_energy.

**Conclusion and proof:** Every-time equality on finite/all nonnegative horizons after those premises. Record stores genuine scalar data rather than equality, but constructing it from physical NSE still requires the cross-testing proof.

### Q5_PORT — `QFA.Assembly.Chain.ReferencePorts`

**Scope:** ASSUMED_PHYSICAL_COMPARISON_AND_ADMISSION_PORT. [Source, lines 46–54](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/Chain.lean#L46-L54).

**Hypotheses:** Every admitted trajectory and reference must have ComparableOnNonnegative; every positive reference shift is a reference and admitted.

**Conclusion and proof:** Supplied comparison data and shift admission. The root consumes these fields; no whole-space PDE constructor was found in inspected chain.

### U5_H3 — `NavierStokesR3.H3Comparison.strong_unique`

**Scope:** ACTUAL_R3_STRONG_STRONG_COMPARISON. [Source, lines 45–76](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/H3CandidateUniqueness.lean#L45-L76).

**Hypotheses:** BOTH u and v are StrongSolutionOnIcc (H3); forcing L2 each interior time; bounded measurable reference spatial derivative; same initial velocity.

**Conclusion and proof:** Pointwise equality on entire closed slab; arbitrary C1 pressure potentials. Derives pressure-gradient L2 from actual PDE and pressure orthogonality from H1/divergence. Despite weak–strong comment, competitor still has H3 class and actual L2 time derivative, so not LH weak–strong uniqueness.

### U5_SMOOTH — `NavierStokesR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc`

**Scope:** ACTUAL_R3_SMOOTH_COMPARISON_WITH_COMPACT_REFERENCE. [Source, lines 30–68](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/WholeSpaceUniqueness.lean#L30-L68).

**Hypotheses:** ν=1 residual equality (same force); BOTH velocities/pressures smooth on closed slab; one common compact support for reference velocity; competing velocity uniformly finite-energy; both divergence free; same initial data.

**Conclusion and proof:** Pointwise equality on closed slab; no pressure normalization or pressure growth bound. Derives pressure recovery/flux and comparison estimates from actual equation. Competitor is smooth, not LH, and reference support is restrictive.

### M5_ODE — `ODE_solution_unique_of_mem_Icc_right`

**Scope:** GENERIC_ODE_UNIQUENESS_PRIMITIVE. [Source, lines 194–205](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/ODE/ExistUnique.lean#L194-L205).

**Hypotheses:** Lipschitz vector field, continuous trajectories, right derivatives, region membership and same initial value.

**Conclusion and proof:** Equality of ordinary ODE solutions. Not a substitute for LH cross-testing/relative-energy uniqueness.


## Step 6: Small energy–enstrophy product bootstrap and global strong restart

### P6_SMALL — `QuasiFeffermanB.SPECTRAL_H1_CALORIC_BUDGET; EXACT_H1_ADMISSION_UNCONDITIONAL`

**Scope:** ACTUAL_PERIODIC_SMALL_DATA. [Source, lines 21–55](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/_vendor/QuasiFeffermanB/CaloricNumericalAdmission.lean#L21-L55).

**Hypotheses:** ν>0; expanding ExactH1Admission requires actual periodic physical H1, EnergySigmaZero, physicalHalfEnergy b < 2πν².

**Conclusion and proof:** Nonempty actual global RegularReference with exact strong trace and finite-horizon L4L6. Proves uniform finite caloric budget from exact numerical smallness then physical H1 admission; the final theorem has no budget or existence certificate premise. Exact external audit found separately in Methlib43535278019.

### P6_REFERENCE — `QuasiFeffermanB.RegularReference; ExactH1Admission`

**Scope:** PERIODIC_PHYSICAL_SMALL_DATA_CONTRACT. [Source, lines 18–31](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/_vendor/QuasiFeffermanB/RegularReference.lean#L18-L31).

**Hypotheses:** Physical H1 datum, solenoidal/mean-zero L2 representative, small physicalHalfEnergy.

**Conclusion and proof:** Reference contains CriticalPositiveSobolevFlow (actual periodic NSE), strong L2 trace, and L4L6 on every finite positive horizon. Expanded contract prevents misreading theorem name as unrestricted H1 global existence.

### P6_HHALF — `SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL`

**Scope:** ACTUAL_PERIODIC_SMALL_DATA. [Source, lines 18–53](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/_vendor/SingularClosure/NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL.lean#L18-L53).

**Hypotheses:** ν>0; a:CriticalSobolev 1 (H-half); CriticalSigmaZero; criticalNonlinearConstant*‖a‖<ν.

**Conclusion and proof:** Actual regular solution with LH membership, LH uniqueness, positive-time smooth NSE and global regularity budgets. Assembles previously proved critical small-data construction; periodic spectral carrier.

### P6_RATE — `MethbokeAddon.WeakFouriermanB.initial_front_physicalEnstrophy_hasDerivAt; INITIAL_FRONT_PHYSICAL_ENSTROPHY_CUBIC`

**Scope:** ACTUAL_PERIODIC_BALANCE. [Source, lines 251–340](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/MethbokeAddon/WeakFouriermanB/PhysicalEnstrophyEvolution.lean#L251-L340).

**Hypotheses:** Actual InitialClassicalFront; t in (0,T), ν>0 for the cubic inequality.

**Conclusion and proof:** Actual enstrophy derivative and Y′+νZ≤Cν^-3 Y³. Actual PDE, differentiation under the unit-cube integral, periodic integration by parts and pressure cancellation.

### P6_NONLINEAR — `MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_THREE_QUARTER_BOUND; PHYSICAL_NONLINEAR_ABSORPTION`

**Scope:** ACTUAL_PERIODIC_ESTIMATE. [Source, lines 208–286](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/MethbokeAddon/WeakFouriermanB/PhysicalNonlinear.lean#L208-L286).

**Hypotheses:** Smooth periodic mean-zero field; ν>0 in absorption.

**Conclusion and proof:** Convection bound C Y^(3/4)Z^(3/4), then 2N≤νZ+Cν^-3Y³. Uses periodic Sobolev/Poincaré chain. This is not the requested R3 energy–enstrophy product estimate or its numerical constant.

### Q6_SCALAR — `QFA.Endpoints.Agmon.ScalarProfile`

**Scope:** EXPLICIT_SCALAR_ANALYTIC_HYPOTHESES. [Source, lines 39–47](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Agmon/Scalar.lean#L39-L47).

**Hypotheses:** E,D,Z,A,N≥0; D²≤EZ; A²≤sqrt(DZ)/(2π); N≤A sqrt(D) sqrt(Z).

**Conclusion and proof:** Data for scalar fourth-power convection estimate. Each analytic estimate is a structure field, not silently proved by this scalar record.

### Q6_ABSORPTION — `QFA.Endpoints.Agmon.nonlinearCoefficient_lt_viscosity; ScalarProfile.enstrophy_absorption; ScalarProfile.viscosity_margin_pos`

**Scope:** REUSABLE_POINTWISE_SCALAR_PROOF. [Source, lines 142–212](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Agmon/Scalar.lean#L142-L212).

**Hypotheses:** ScalarProfile; small ED<4π²ν⁴, ν>0 for strict margin; supplied scalar d/2+νZ≤N.

**Conclusion and proof:** N≤c(E,D)Z and d+2(ν−c)Z≤0 with positive margin. Exact nested square root/fourth-power algebra includes zero cases. d is only a real number here; no HasDerivAt, actual NSE balance, invariant over time or continuation is proved.

### Q6_CORRECTED — `QFA.CorrectedPhysicalRoot.exists_absorption_of_compactSchwartzData; correctedPointwiseAbsorption_of_analytic_inputs`

**Scope:** CONDITIONAL_FULL_VOLUME_POINTWISE_ANALYTIC_PROOF. [Source, lines 62–112](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/CorrectedPhysicalRoot/QFACorrectedRoot/Analytic.lean#L62-L112).

**Hypotheses:** WholeSpaceSpectralEndpoint; WholeSpaceAgmonEndpoint; compact-Schwartz derivative witnesses; convection estimate; actual L2 energy smallness; supplied scalar enstrophy inequality.

**Conclusion and proof:** Positive absorption margin and exact fourth-power nonlinear estimate for actual L2 fields. Uses compact-Schwartz density/extension bridge, supplied spectral/Agmon endpoints, complexification norm identities and scalar absorption. No time-evolution construction.

### Q6_BACKEND — `QFA.CorrectedPhysicalRoot.CorrectedReferenceConstructionFromAbsorption`

**Scope:** ASSUMED_LOCAL_EVOLUTION_AND_GLOBAL_CONTINUATION_PORT. [Source, lines 114–125](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/CorrectedPhysicalRoot/QFACorrectedRoot/Analytic.lean#L114-L125).

**Hypotheses:** A function from CorrectedPointwiseAbsorption ν to SubcriticalReferenceConstruction.

**Conclusion and proof:** Would return a global reference for a selected subcritical restart. Comment and type leave physical derivative realization, local strong evolution, temporal invariant and continuation explicit.

### Q6_REFERENCE — `QFA.Assembly.Chain.SubcriticalReferenceConstruction`

**Scope:** ASSUMED_REFERENCE_EXISTENCE_PORT. [Source, lines 148–157](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/Chain.lean#L148-L157).

**Hypotheses:** For every admitted trajectory and selected good start with energy start, RestartData and ED<4π²ν⁴.

**Conclusion and proof:** ∃v, Reference(u s)v. No inhabitant of this construction input was located in the inspected sources; this is the input used by tail assembly, not a theorem proving arbitrary H1 existence.

## Conditional root and exact ports

`QFA.CorrectedPhysicalRoot.QUASI_FEFFERMAN_A_CORRECTED` at [PhysicalRoot.lean131–158](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/CorrectedPhysicalRoot/QFACorrectedRoot/PhysicalRoot.lean#L131-L158) takes `ClassRealization`, `ReferencePorts`, `WholeSpaceSpectralEndpoint`, `WholeSpaceAgmonEndpoint`, `CorrectedReferenceConstructionFromAbsorption` and `SmoothReferencePorts`. Domain, Admissible, Reference, Good and SmoothNSETail remain supplied predicates. The theorem proves their composition; it does not identify those predicates with actual whole-space NSE classes.

The key obstruction for steps3–6 is not missing scalar Grönwall or Hilbert trace machinery. It is inhabiting the concrete PDE interfaces: actual R3 LH nonemptiness/restart membership, actual relative-energy cross-testing, and a strong reference constructed from the selected H1 datum and continued using a preserved small-product bound.

## Cached evidence and its scope

The native exact audit receipt is source fdb515d8, [external Linux CI run44566880192](https://github.com/randogelist/Methboke/actions/runs/44566880192), Lean4.33.0, Mathlibdb584. The selected log hashes were checked against the receipt and exact printed theorem types/axiom lists were read. The cited native audits report only `propext`, `Classical.choice`, `Quot.sound`. The JSON preserves each selected exact printed type and audit SHA256.

The numerical periodic admission also has an exact saved audit at Methlib `Quasi-Fefferman-B/evidence/run-43535278019-exact/qfb/QuasiFeffermanB_CaloricNumericalAdmission-axioms.log`, lines19–22. The manifest SHA256 for its source equals current vendor and pinned fdb source. That historical package status still marks the root PENDING; the evidence cited here is the named declaration audit.

The QFA top README reports LE001–LE108 accepted at9b6ca616/run43532773061. The corrected-root saved report gives conditional PASS, unconditional FALSE, CR001–CR007, compiled41188cef/run43554315545 and standard axioms only. Parent synthesis owns exact raw-evidence/source correspondence. These receipts cannot turn an explicit input port into a proved physical constructor.

## Transfer cautions

- Periodic physical proofs use volume.restrict unitCube, periodic velocity/pressure, mean-zero and often Poincare. They are actual physical PDE proofs in that scope, not finite Galerkin-only results, but cannot be silently transferred to R3.
- QFA historical cutoff is ||a||^4/(16*pi^2*nu^5), with ED<4*pi^2*nu^4. Current requested cutoff8/(27*pi^4) has different normalization/constant and needs separate derivation.
- Current Complexification.lean RealTestWeakDirectionalDerivative quantifies all compactly supported smooth real tests. Do not repeat stale comments describing its current type as radial-only. Corrected compact-Schwartz bridge is an explicit interface change, not evidence of a current radial-only definition.
- Upstream source belongs to a different toolchain/Mathlib pin and only source was inspected here. No matching external audit was independently recovered for those upstream declarations.
- Native receipts are Linux external CI, not native Windows. QFA cached report identifies Windows compiler.
- No generic Mathlib NSE/Leray-Hopf theorem was found by bounded source search in the pinned Mathlib. This is a bounded search finding, not a universal nonexistence claim.

No Lean, Lake, kernel, project runner or downloaded project code was executed. All work was source reading, static archive extraction, hashing and report preparation.
