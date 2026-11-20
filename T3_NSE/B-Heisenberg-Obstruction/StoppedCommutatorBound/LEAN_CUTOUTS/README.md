# Ehrenfest identity cutouts

**60 source-exact reference cutouts:** the 53 indexed declarations plus seven nearby support identities, taken from 36 pinned source modules. Each entry includes its original declaration/proof text, consumer import, source line range, source hash, reuse boundary and inherited evidence status. Full source snapshots preserve the surrounding helpers, scopes and original headers.

Start with [FAST_IDENTITIES.md](FAST_IDENTITIES.md), ordered for the nine-module scalar route. Use the original imports to reuse declarations. The raw `.lean.txt` files are readable/copyable reference excerpts; they are not standalone compiled modules. No copied proof or new theorem has been compiled in this collection.

- [Fast-route identities](FAST_IDENTITIES.md) and [minimal consumer imports](FAST_IMPORTS.lean.txt)
- [All consumer imports and reference checks](IMPORTS.lean.txt)
- [Machine identity catalog](IDENTITIES.json), [full-source manifest](SOURCES.json), [static validation](VALIDATION.json)
- [New adapters still needed](REMAINING_ADAPTERS.md)
- [Current B-tier route](../PREPRINT_FORMALISATION/FAST_ROUTE.md)

The original seven named external audits remain attached only to their exact original declarations. Thirteen other entries have source review in accepted native modules; forty are source-only records, including the seven companions. Copying them creates no new formal acceptance. The existing audited QFB cutout in the parent directory is unchanged.

## Full catalog

| ID | Existing declaration | Original evidence | Source |
|---|---|---|---|
| [ML01](cards/ML01.md) | `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` | Source only | [S13](sources/S13_ExistUnique.lean.txt) |
| [ML02](cards/ML02.md) | `ODE_solution_unique_of_mem_Icc` | Source only | [S13](sources/S13_ExistUnique.lean.txt) |
| [ML03](cards/ML03.md) | `le_gronwallBound_of_liminf_deriv_right_le` | Source only | [S14](sources/S14_Gronwall.lean.txt) |
| [ML05](cards/ML05.md) | `HasFDerivAt.comp_hasDerivAt` | Source only | [S05](sources/S05_Comp.lean.txt) |
| [ML06](cards/ML06.md) | `HasDerivAt.inv` | Source only | [S06](sources/S06_Inv.lean.txt) |
| [ML08](cards/ML08.md) | `HasDerivAt.norm_sq` | Source only | [S10](sources/S10_Calculus.lean.txt) |
| [ML10](cards/ML10.md) | `HasFDerivAt.smul` | Source only | [S08](sources/S08_Mul.lean.txt) |
| [ML12](cards/ML12.md) | `ContDiff.mul` | Source only | [S03](sources/S03_Operations.lean.txt) |
| [ML13](cards/ML13.md) | `Convex.image_sub_le_mul_sub_of_deriv_le` | Source only | [S07](sources/S07_MeanValue.lean.txt) |
| [ML15](cards/ML15.md) | `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable` | Source only | [S17](sources/S17_IntegralEqImproper.lean.txt) |
| [ML16](cards/ML16.md) | `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` | Source only | [S16](sources/S16_Jacobian.lean.txt) |
| [ML17](cards/ML17.md) | `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` | Source only | [S16](sources/S16_Jacobian.lean.txt) |
| [ML18](cards/ML18.md) | `ContDiffBump.integral_normed` | Source only | [S01](sources/S01_Normed.lean.txt) |
| [ML19](cards/ML19.md) | `ContDiffBump.hasCompactSupport_normed` | Source only | [S01](sources/S01_Normed.lean.txt) |
| [ML20](cards/ML20.md) | `HasCompactSupport.hasFDerivAt_convolution_right` | Source only | [S02](sources/S02_Convolution.lean.txt) |
| [MLB01](cards/MLB01.md) | `SingularClosure.invariantGalerkinSubspace` | Accepted module; source review | [S33](sources/S33_GalerkinInvariant.lean.txt) |
| [MLB02](cards/MLB02.md) | `SingularClosure.contDiff_invariantGalerkinRhs` | Accepted module; source review | [S33](sources/S33_GalerkinInvariant.lean.txt) |
| [MLB03](cards/MLB03.md) | `SingularClosure.invariantGalerkinRhs_inner` | Accepted module; source review | [S33](sources/S33_GalerkinInvariant.lean.txt) |
| [MLB04](cards/MLB04.md) | `SingularClosure.invariantGalerkinRhs_global_exists` | Accepted module; source review | [S33](sources/S33_GalerkinInvariant.lean.txt) |
| [MLB05](cards/MLB05.md) | `SingularClosure.finiteGalerkinRhs_unique_on_Icc` | Accepted module; source review | [S32](sources/S32_GalerkinExistence.lean.txt) |
| [MLB06](cards/MLB06.md) | `SingularClosure.coefficientNonlinearPower_eq_zero` | Accepted module; source review | [S31](sources/S31_GalerkinEnergy.lean.txt) |
| [MLB07](cards/MLB07.md) | `SingularClosure.GalerkinSolution.coefficientEnergy_identity` | Accepted module; source review | [S31](sources/S31_GalerkinEnergy.lean.txt) |
| [MLB08](cards/MLB08.md) | `SingularClosure.GalerkinSolution.coefficientEnstrophy_identity` | Accepted module; source review | [S29](sources/S29_EnstrophyInequality.lean.txt) |
| [MLB09](cards/MLB09.md) | `SingularClosure.coefficientEnstrophyNonlinearPower_eq_physical` | Accepted module; source review | [S35](sources/S35_PhysicalBilinear.lean.txt) |
| [MLB10](cards/MLB10.md) | `SingularClosure.GalerkinSolution.coefficientDissipation_initial_le` | Accepted module; source review | [S34](sources/S34_InitialCutoffBounds.lean.txt) |
| [MLB11](cards/MLB11.md) | `SingularClosure.GalerkinSolution.sobolevState_H1_physical_norm_sq` | Accepted module; source review | [S36](sources/S36_TorusGalerkinSobolev.lean.txt) |
| [MLB12](cards/MLB12.md) | `SingularClosure.canonicalGalerkinSolution` | Accepted module; source review | [S27](sources/S27_CanonicalGalerkin.lean.txt) |
| [MLB13](cards/MLB13.md) | `SingularClosure.CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE` | Named external audit | [S28](sources/S28_CriticalGalerkin.lean.txt) |
| [MLB14](cards/MLB14.md) | `SingularClosure.SOBOLEV_DIVERGENCE_PRODUCT_NORM_BOUND` | Accepted module; source review | [S30](sources/S30_FourierSobolevProduct.lean.txt) |
| [MLB15](cards/MLB15.md) | `MethbokeAddon.WeakFouriermanB.global_smooth_to_initial_front` | Named external audit | [S23](sources/S23_LocalClassicalUniqueness.lean.txt) |
| [MLB16](cards/MLB16.md) | `MethbokeAddon.WeakFouriermanB.initial_classical_front_unique` | Named external audit | [S23](sources/S23_LocalClassicalUniqueness.lean.txt) |
| [MLB17](cards/MLB17.md) | `MethbokeAddon.WeakFouriermanB.initial_physicalDissipation_continuousOn_Icc` | Named external audit | [S26](sources/S26_PhysicalEnstrophyEvolution.lean.txt) |
| [MLB18](cards/MLB18.md) | `MethbokeAddon.WeakFouriermanB.initial_front_physicalEnstrophy_hasDerivAt` | Named external audit | [S26](sources/S26_PhysicalEnstrophyEvolution.lean.txt) |
| [MLB19](cards/MLB19.md) | `MethbokeAddon.WeakFouriermanB.galerkin_uniform_local_sobolev_bounds` | Named external audit | [S24](sources/S24_LocalGalerkinBounds.lean.txt) |
| [MLB20](cards/MLB20.md) | `MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_pointwise` | Named external audit | [S25](sources/S25_LocalGalerkinRegularity.lean.txt) |
| [OP01](cards/OP01.md) | `LinearPMap` | Source only | [S15](sources/S15_LinearPMap.lean.txt) |
| [OP02](cards/OP02.md) | `LinearPMap.graph` | Source only | [S15](sources/S15_LinearPMap.lean.txt) |
| [OP03](cards/OP03.md) | `LinearPMap.isClosable_iff_exists_closed_extension` | Source only | [S18](sources/S18_LinearPMap.lean.txt) |
| [OP04](cards/OP04.md) | `LinearPMap.closure` | Source only | [S18](sources/S18_LinearPMap.lean.txt) |
| [OP05](cards/OP05.md) | `LinearPMap.IsClosable.closure_isClosed` | Source only | [S18](sources/S18_LinearPMap.lean.txt) |
| [OP06](cards/OP06.md) | `LinearPMap.HasCore` | Source only | [S18](sources/S18_LinearPMap.lean.txt) |
| [OP07](cards/OP07.md) | `LinearPMap.IsFormalAdjoint` | Source only | [S11](sources/S11_LinearPMap.lean.txt) |
| [OP08](cards/OP08.md) | `LinearPMap.IsFormalAdjoint.le_adjoint` | Source only | [S11](sources/S11_LinearPMap.lean.txt) |
| [OP09](cards/OP09.md) | `LinearPMap.adjoint_isClosed` | Source only | [S11](sources/S11_LinearPMap.lean.txt) |
| [OP10](cards/OP10.md) | `LinearPMap.isSelfAdjoint_def` | Source only | [S11](sources/S11_LinearPMap.lean.txt) |
| [OP11](cards/OP11.md) | `TestFunction` | Source only | [S09](sources/S09_TestFunction.lean.txt) |
| [OP12](cards/OP12.md) | `MeasureTheory.Lp.dense_hasCompactSupport_contDiff` | Source only | [S12](sources/S12_SmoothApprox.lean.txt) |
| [FAST01](cards/FAST01.md) | `MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_ABSORPTION` | Source only | [S19](sources/S19_PhysicalNonlinear.lean.txt) |
| [FAST02](cards/FAST02.md) | `SingularClosure.FINITE_FOURIER_H2_L1_BOUND` | Source only | [S21](sources/S21_LatticeSobolevSummability.lean.txt) |
| [FAST03](cards/FAST03.md) | `SingularClosure.torusSobolevMultiplierLinear_norm_le` | Source only | [S20](sources/S20_FourierSobolevOperators.lean.txt) |
| [FAST04](cards/FAST04.md) | `SingularClosure.coefficientEnergy_le_dissipation` | Source only | [S22](sources/S22_PeriodicSobolev.lean.txt) |
| [FAST05](cards/FAST05.md) | `SingularClosure.torusSobolevLeray_norm_le` | Source only | [S20](sources/S20_FourierSobolevOperators.lean.txt) |
| [ML21](cards/ML21.md) | `exists_hasDerivAt_eq_slope` | Source only | [S07](sources/S07_MeanValue.lean.txt) |
| [AUX01](cards/AUX01.md) | `SingularClosure.finiteSobolev_H1_physical_norm_sq` | Source only | [S36](sources/S36_TorusGalerkinSobolev.lean.txt) |
| [AUX02](cards/AUX02.md) | `HasDerivWithinAt.inv` | Source only | [S06](sources/S06_Inv.lean.txt) |
| [AUX03](cards/AUX03.md) | `HasDerivWithinAt.norm_sq` | Source only | [S10](sources/S10_Calculus.lean.txt) |
| [AUX04](cards/AUX04.md) | `HasDerivWithinAt.mono` | Source only | [S04](sources/S04_Basic.lean.txt) |
| [AUX05](cards/AUX05.md) | `HasDerivWithinAt.hasDerivAt` | Source only | [S04](sources/S04_Basic.lean.txt) |
| [AUX06](cards/AUX06.md) | `HasDerivWithinAt.continuousWithinAt` | Source only | [S04](sources/S04_Basic.lean.txt) |
| [AUX07](cards/AUX07.md) | `HasDerivWithinAt.continuousOn` | Source only | [S04](sources/S04_Basic.lean.txt) |

## Source fidelity and use

The raw cutouts are exact contiguous source slices, including proof bodies or definition fields. Companion entries do not alter the existing 53-anchor index. Source snapshots retain each complete file byte-for-byte; their imports are recorded separately. The manifest preserves contextual review excerpts for Mathlib declarations with hidden section parameters or local instances.

The collection does not flatten dependencies. Reuse by importing the listed original module and calling its existing declaration; later formalization must provide each literal hypothesis. Any future separately reconstructed cutout needs matching external cached elaboration and an exact type/axiom audit. No local Lean, Lake or kernel execution is permitted.

Mathlib sources retain their original copyright headers and are distributed under the included [Apache 2.0 license](LICENSE.mathlib). Project/vendor sources are pinned in the source manifest. See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
