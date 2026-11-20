# NSE-A Lean gap and cutout collection

**51 exact reference cutouts**, with **60 byte-preserved source snapshots** covering **58 distinct original modules** and **130 selected declaration entries**. Five additional external source leads are recorded by exact revision and URL. This collection adds no native Lean theorem or A-tier acceptance.

The source basis is `ce7f809ad20b3498a63420a22d17b3c801dfd558` on `AC-Integration`. The project goal remains Fefferman D; this is scoped source acquisition for the registered NSE-A regularity class.

## Start here

- [Largest logical gaps and improved proof route](GAPS.md)
- [Gap-to-cutout map](GAPS.json)
- [Complete source and proof-boundary catalog](IDENTITIES.json)
- [Full-source provenance](SOURCES.json) and [compiler/dependency environments](SOURCE_ENVIRONMENTS.json)
- [Additional inspected source leads](SOURCE_LEADS.json)
- [Static fidelity checks](VALIDATION.json)
- [Cumulative B-tier TXT with these references](../NSE_A_A_TIER_STEPLIST_B_TIER.txt)

## What was attained

The strongest new source additions are real compact-test separation and complete equalizers; spectral H1 derivative witnesses and both weighted-Fourier membership directions; bounded measurable L2 multipliers; an L2 reality-symmetry proof; whole-space H1 convection identities; and a better scalar route through the already audited integral Gronwall theorem.

The substantial unresolved constructions remain actual R3 H1 local/maximal theory, the registered sharp Sobolev constant, actual PDE time evolution, the native physical H1/Fourier/projector adapters, and the literal smooth finite-energy solution-class bridge. The gap statements concern these inspected sources and this target. They are not assertions about every Lean repository.

## Evidence classification

| Existing evidence for each selected cutout block | Blocks |
|---|---:|
| Exact previously named scoped external audit | 21 |
| Previously compiled module; selected endpoint lacks a directly named audit | 3 |
| Pinned Mathlib source inspected | 14 |
| Other pinned source inspected, under different environments | 13 |

These are source/evidence classifications, not counts of new accepted endpoints. Historical comments inside copied modules remain byte-preserved; the catalog records the reviewed evidence separately. Existing acceptance remains tied to its exact original type and hypotheses.

## Recommended reading order

1. **SP01–SP03:** native physical contracts, closed graph machinery and real compact-test separation.
2. **SP17, SP18, SP21, then SP05:** external H1 spectral witnesses and membership equivalences compared with the native combined-gradient/Laplacian interface.
3. **SP19, SP20, SP06–SP09:** measurable multipliers, Fourier reality and L2 representation. SP20 contains private proof templates.
4. **ES02–ES06:** AC fundamental theorem, accepted integral Gronwall, energy envelope/product and strict good-time selection.
5. **EV02–EV08:** actual periodic local construction, maximal development and restart patterns, retaining their domain and data assumptions.
6. **ES01, ES13–ES16:** the precise current spatial-estimate boundary. L6 membership and an L-infinity-test convection estimate do not admit the displayed sharp constant.
7. **EV09–EV14 and SOURCE_LEADS:** pressure, supplied H3 solutions, comparison and the remaining A4 category/endpoint obligations.

## Full cutout catalog

Each card links the exact slice, the full original source, its pinned URL, import context, proof scope and remaining obligation.

| ID | First selected declaration (companions on the card) | Plan | Evidence |
|---|---|---|---|
| [SP01](cards/SP01.md) | `MethbokeAddon.QuasiFeffermanA.Space` | P01, P02, P05 | Prior named scoped audit |
| [SP02](cards/SP02.md) | `ContinuousLinearMap.isClosed_ker` | P01 | Pinned Mathlib source |
| [SP03](cards/SP03.md) | `ae_eq_zero_of_integral_contDiff_smul_eq_zero` | P01, P02 | Pinned Mathlib source |
| [SP04](cards/SP04.md) | `QFA.Endpoints.Representation.CompactSchwartz.denseCompactSchwartzTests` | P02 | Prior named scoped audit |
| [SP05](cards/SP05.md) | `MethbokeAddon.QuasiFeffermanA.FourierMultipliers.ae_eq_of_const_smul_real_multiplier_distribution` | P02, P05 | Prior named scoped audit |
| [SP06](cards/SP06.md) | `MeasureTheory.Lp.fourierTransformₗᵢ` | P02, P04, P06 | Pinned Mathlib source |
| [SP07](cards/SP07.md) | `MeasureTheory.eLpNorm_indicator_le` | P03, P04 | Pinned Mathlib source |
| [SP08](cards/SP08.md) | `MeasureTheory.Lp.compMeasurePreserving` | P04 | Pinned Mathlib source |
| [SP09](cards/SP09.md) | `ContinuousLinearMap.compLp` | P01, P04 | Pinned Mathlib source |
| [SP10](cards/SP10.md) | `QFA.LC001SpectralReduction.integrable_norm_sq` | P06 | Prior named scoped audit |
| [SP11](cards/SP11.md) | `Finset.sum_sq_le_sq_sum_of_nonneg` | P07 | Pinned Mathlib source |
| [SP12](cards/SP12.md) | `MeasureTheory.lintegral_iSup'` | P08 | Pinned Mathlib source |
| [SP13](cards/SP13.md) | `MeasureTheory.lintegral_finsetSum'` | P08 | Pinned Mathlib source |
| [SP14](cards/SP14.md) | `MeasureTheory.lintegral_ofReal_ne_top_iff_integrable` | P08 | Pinned Mathlib source |
| [SP15](cards/SP15.md) | `MeasureTheory.ofReal_integral_eq_lintegral_ofReal` | P08 | Pinned Mathlib source |
| [SP16](cards/SP16.md) | `ENNReal.rpow_eq_top_iff_of_pos` | P08 | Pinned Mathlib source |
| [SP17](cards/SP17.md) | `LerayHopf.gradComp_of_memH1` | P01, P02, P05 | External source; different pins |
| [SP18](cards/SP18.md) | `LerayHopf.memLp_sqrtWeight_smul_fourier` | P02, P05, P06 | External source; different pins |
| [SP19](cards/SP19.md) | `LerayHopf.BoundedMultiplier.memLp_mulBdd` | P04, P05, P06 | External source; different pins |
| [SP20](cards/SP20.md) | `LerayHopf.reflect_fourier_schwartzC_eq_conj` | P04 | External source; different pins |
| [SP21](cards/SP21.md) | `LerayHopf.memSobolev_of_finite_weightedFourier_R3` | P01, P02, P05 | External source; different pins |
| [ES01](cards/ES01.md) | `MeasureTheory.eLpNormLESNormFDerivOfEqInnerConst` | P09 | Pinned Mathlib source |
| [ES02](cards/ES02.md) | `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` | P12, P13, P15 | Pinned Mathlib source |
| [ES03](cards/ES03.md) | `QFA.Endpoints.Comparison.CRITICAL_RELATIVE_ENERGY_GRONWALL` | P13, P15 | Prior named scoped audit |
| [ES04](cards/ES04.md) | `QFA.Energy.envelope_absolutelyContinuousOnInterval` | P12 | Prior named scoped audit |
| [ES05](cards/ES05.md) | `QFA.Energy.product_budget_Ioo` | P12, P16 | Prior named scoped audit |
| [ES06](cards/ES06.md) | `MethbokeAddon.QuasiFeffermanA.safeCutoff_eq_pi_formula_of_sixth_power` | P09, P16 | Prior named scoped audit |
| [ES07](cards/ES07.md) | `SingularClosure.CUBIC_ENERGY_OF_SQUARE_BUDGET` | P13, P15 | Prior compiled module only |
| [ES08](cards/ES08.md) | `MethbokeAddon.WeakFouriermanB.initial_front_physicalEnstrophy_hasDerivAt` | P13 | Prior named scoped audit |
| [ES09](cards/ES09.md) | `MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_dissipation_square` | P15 | Prior named scoped audit |
| [ES10](cards/ES10.md) | `MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_dissipation_square` | P15 | Prior named scoped audit |
| [ES11](cards/ES11.md) | `MethbokeAddon.WeakFouriermanB.initial_front_extends_of_dissipation_square` | P11, P15, P17 | Prior named scoped audit |
| [ES12](cards/ES12.md) | `QFA.Endpoints.Agmon.ScalarProfile.enstrophy_absorption` | P13, P14 | Prior named scoped audit |
| [ES13](cards/ES13.md) | `LerayHopf.gns_L6_of_memH1_R3` | P01, P09 | External source; different pins |
| [ES14](cards/ES14.md) | `LerayHopf.convFormH1_integrable` | P09, P12, P13 | External source; different pins |
| [ES15](cards/ES15.md) | `LerayHopf.convFormH1_ibp` | P12, P13 | External source; different pins |
| [ES16](cards/ES16.md) | `LerayHopf.convIntegralSchwartz_bound_H1` | P09, P12, P13 | External source; different pins |
| [EV01](cards/EV01.md) | `MethbokeAddon.WeakFouriermanB.InitialClassicalFront` | P10, P11, P19 | Prior compiled module only |
| [EV02](cards/EV02.md) | `MethbokeAddon.WeakFouriermanB.uniform_H1_local_initial_classical_front_exists` | P10 | Prior named scoped audit |
| [EV03](cards/EV03.md) | `MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_uniform_H2` | P10 | Prior named scoped audit |
| [EV04](cards/EV04.md) | `MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initialClassicalFront` | P10, P19 | Prior named scoped audit |
| [EV05](cards/EV05.md) | `MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_front` | P11 | Prior named scoped audit |
| [EV06](cards/EV06.md) | `MethbokeAddon.WeakFouriermanB.maximal_classical_front_unique` | P11 | Prior named scoped audit |
| [EV07](cards/EV07.md) | `MethbokeAddon.WeakFouriermanB.initial_front_extend_from_restart` | P11 | Prior named scoped audit |
| [EV08](cards/EV08.md) | `MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_eq_top_of_uniform_H1` | P11, P15 | Prior named scoped audit |
| [EV09](cards/EV09.md) | `MethbokeAddon.WeakFouriermanB.normalized_pressure_eq_of_gradient_eq` | P19 | Prior named scoped audit |
| [EV10](cards/EV10.md) | `NavierStokesR3.H3Comparison.StrongSolutionOnIcc` | P10, P19 | External source; different pins |
| [EV11](cards/EV11.md) | `NavierStokesR3.H3Comparison.StrongSolutionOnIcc.pressureGradient_memLp` | P19 | External source; different pins |
| [EV12](cards/EV12.md) | `NavierStokesR3.H3Comparison.strongSolution_of_compact_slab` | P10, P19 | External source; different pins |
| [EV13](cards/EV13.md) | `NavierStokesR3.H3Comparison.strong_unique` | P11, P19 | External source; different pins |
| [EV14](cards/EV14.md) | `QFA.Assembly.Integrated.ReferenceConstructionFromAbsorption` | P10, P11 | Prior compiled module only |

## Reuse and acceptance boundary

The `.lean.txt` excerpts are exact contiguous source slices, including their selected statements and proof bodies. Full snapshots preserve original headers, imports, earlier helpers and surrounding scopes. Dependencies have not been flattened. The files are reference material outside `Material/`; they are not standalone compiled modules or newly registered build packages.

Use an existing public declaration through its original module and satisfy its literal hypotheses. Private proof bodies require an explicit owned adaptation before reuse. External source uses different compiler/Mathlib pins, so successful native transport still needs matching authorized cached external compilation, expected-type checks and named axiom reports. No local Lean, Lake, kernel audit or project runner was executed.

The licenses for Mathlib, uda-lab/leray-hopf and OpenAI/NavierStokesAndEuler are preserved alongside the full modules. See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). The additional Buckmaster leads are metadata and links only.
