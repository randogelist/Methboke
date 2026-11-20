# Spatial source anchors for QFA/QFB steps 1–2

## Result

There are genuine reusable whole-space foundations in the exact Mathlib pin and substantive native whole-space adapters in the recovered Methlib QFA source. The list can therefore be filled with precise imports and intermediate theorems. It cannot yet be marked complete: the chosen actual R³ H¹/Leray–Hopf semantics, the required Sobolev extension and sharp constant, and the final physical H² Hessian identity still need matching native statements and proofs.

This report is static source inspection plus reading retained external evidence. No Lean, Lake, local kernel audit, or project runner was executed. No new proof or PDE assumption record was introduced. The machine-readable companion contains 38 anchors, exact source excerpts and hypotheses, per-file SHA256 hashes, five remaining obligations, and the passive import/check list.

## Pins and evidence

- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`; source tar SHA256 `963f31efd321dea2e38178eb3b8161ded7f2be5678aa5e3f0954b1372329bd0c`.
- Methboke periodic reference: `fdb515d8bde35ec8021bbc26f360aca8dfa2855c`, Lean `v4.33.0`, the same Mathlib pin. The retained run `44566880192` reports PASS. Selected current QFB/operator/nonlinear files were byte-compared with the frozen export. `WFBPhysicalNonlinear` expressly audits the periodic Hessian and L⁶ declarations with only `propext`, `Classical.choice`, and `Quot.sound`.
- Methlib whole-space QFA: `53b2318c2b586137b6db74c4d3a41bb0b964b2d8`. The source provenance review records all 34 LeanEndpoints source/config files match retained `9b6ca616…` evidence, with 108 audited declarations using standard axioms. Separate LC004/LC005/corrected-root source matching is recorded in ../SOURCE_REVIEW.json; source availability is not confused with a newly executed check.
- October v11 ZIP SHA256: `bddd0a0b0a6a38b343002bf141e902bfb1cf8664770e910882778f4037bdefb8`. v25 ZIP SHA256: `463dec3a7e1638c5e078dcfe732a9648a8ed129ce3dc7ec54b9aaa949b42e19c`.

## Step 1: concrete semantics

**Direct building blocks exist.** Mathlib `Lp` is an actual a.e.-equivalence-class space; `MemLp.toLp_eq_toLp_iff` identifies its equality with a.e. equality. Use full `volume` on `EuclideanSpace ℝ (Fin 3)`, rather than the QFB cube restriction. `EuclideanSpace.real_norm_sq_eq` fixes the physical vector norm. SingularClosure's `coordinateDerivative`, `divergence`, `gradient`, `laplacian`, and `convection` are real differential operators whose definitions themselves do not require periodicity.

**Methlib already supplies important native work.** `QFA.Endpoints.Representation.complexifyVectorLI` and `complexifyL2LI` are genuine real linear isometries into complex Euclidean vectors/L². They preserve summed directional gradient energies without a component-count loss. `RealTestWeakDirectionalDerivative` quantifies all real smooth compactly supported tests, and `complexifyL2_weakDirectionalDerivative` transports this identity after proving test-product integrability. `CompactDerivativeData` supplies first and diagonal-second derivative witnesses with an actual Laplacian sum. These should be reused.

The remaining step is to assemble the actual all-`L²σ(R³)` datum and solution classes, weak gradient/pressure semantics, exact-time traces and the QFA tail predicate. The historical `QFA.PhysicalRoot.QFARoot` still takes arbitrary `Domain`, `Admissible`, and `SmoothNSETail` parameters. Its strict cutoff is `||a||⁴/(16π²ν⁵)`, and its root does not separately state the current tail energy equality. It is a structural predecessor, not the present concrete QFA theorem.

The accepted QFB root remains the periodic specification: every positive viscosity, every solenoidal mean-zero cube L² datum, a nonempty LH class, and every LH velocity/gradient pair; tail smoothness, energy equality and future uniqueness at **δ strictly greater than cutoff**. A separate clause gives smoothness at `safeCutoff = 2*cutoff`. Future uniqueness is from each path's **own exact trace**, not uniqueness from the original rough datum. For zero datum, the safe smooth cutoff is zero; the main QFB energy/uniqueness quantifier remains δ>0.

## Step 2: spatial analysis

**A genuine whole-space critical Sobolev theorem is present.** `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner` assumes a finite-dimensional real normed domain with Haar measure, real Hilbert codomain, `ContDiff ℝ 1 u`, compact support, `1≤p`, positive dimension, and `1/p′=1/p−1/n`. It proves the Lᵖ′ bound by the Lᵖ Fréchet-derivative norm. The case n=3, p=2, p′=6 has exactly the needed exponent relation.

Its constant is `eLpNormLESNormFDerivOfEqInnerConst`, built from a coordinate equivalence and Haar scaling. **It is not a theorem certifying the sharp S₆⁶=16/(27π⁴).** The derivative's operator norm also needs an explicit physical Frobenius-norm bridge, and compact support must be removed for the same H¹ class used by QFA. No completed matching native adapter or sharp Aubin–Talenti constant was located in the reviewed sources. A first version can use a proved admissible constant S, retaining cutoff `S⁶||a||₂⁴/(2ν⁵)`; the advertised numerical cutoff requires the sharp admissibility theorem.

**Interpolation foundations are available.** Mathlib's general-measure Hölder theorem `eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm` and `eLpNorm_norm_rpow` support L²/L⁶→L³. The existing `cube_eLpNorm_three_le_interpolation` is a useful proof template but its statement is tied to the cube. Separately, Methlib's `interpolation_of_nativeSpectralRealization` proves `D²≤EZ` by a nonnegative quadratic/discriminant argument; it still takes the spectral realization and is a different interpolation statement.

**The weak-derivative Fourier route is partly implemented.** LC005 proves compact-support density in the full Schwartz topology, then `schwartzDerivativeWitnesses_of_compactSchwartz_unconditional` removes the density premise from the corrected bridge. LC001 proves `gradient_fourier_ae` and `laplacian_fourier_ae` for actual full-volume L² representatives with the exact 2π multipliers. `nativeSpectralRealization_of_fourierNormAE` derives all integrability and energy identities from two a.e. norm identities. Those norm identities must still be aggregated from the multiplier formulas and composed; the historical corrected root retains `hSpectral` explicitly.

**For the Hessian identity**, Mathlib has whole-space Schwartz integration by parts, Laplacian/basis-derivative identities, second-derivative symmetry, continuous L² Plancherel, and distributional Sobolev machinery. The available native `physical_hessian_laplacian_eq` is an actual externally audited theorem for smooth **periodic** fields and cube integrals. A whole-space Frobenius H² identity for the same actual field/weak derivatives remains to be constructed. This is substantially supported ordinary analysis work, but it is not filled by the periodic theorem's name.

## October official-A interface

v25 `Fefferman.ConcreteReal.realAnalysis` provides actual real derivatives, smoothness and integrals. Its `WholeSpaceAPhysicalPort` contains the **entire global zero-force solution conclusion**, and `WHOLESPACE_A_PHYSICAL_PORT_IFF_A` is a semantic equivalence by unfolding. QFA eventual regularity does not fill this port.

For a later literal-A bridge, retain two explicit compatibility obligations: v25 uses plain `Fin 3 → ℝ` carriers with Euclidean norm supplied separately, and its `timeDerivative` is ambient `deriv` even at zero. A Euclidean coordinate/norm/measure bridge and an initial-time extension/derivative bridge are necessary. These are separate from the positive-time QFA root.

## Key source map

The JSON contains every declaration's exact hypotheses, body excerpts and SHA256. “Direct” below describes a foundation under its stated assumptions, not completion of QFA.

| Anchor | Declaration | Fit | Exact source |
|---|---|---|---|
| `S01-LP` | `MeasureTheory.Lp and companion declarations` | direct | [Mathlib.MeasureTheory.Function.LpSpace.Basic](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean)|
| `S01-EUCLIDEAN` | `EuclideanSpace.norm_sq_eq and companion declarations` | direct | [Mathlib.Analysis.InnerProductSpace.PiL2](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/PiL2.lean)|
| `S01-NATIVE-OPERATORS` | `SingularClosure.Vec and companion declarations` | domain-neutral | [SingularClosure.Contracts](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/_vendor/SingularClosure/Contracts.lean)|
| `M01-COMPLEXIFICATION` | `QFA.Endpoints.Representation.RealL2 and companion declarations` | direct | [QFA.Endpoints.Representation.Complexification](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Representation/Complexification.lean)|
| `M02-WEAK-DERIVATIVE-TESTS` | `QFA.Endpoints.Representation.integrable_compact_test_smul and companion declarations` | direct | [QFA.Endpoints.Representation.Complexification](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LeanEndpoints/QFA/Endpoints/Representation/Complexification.lean)|
| `M04-COMPACT-SCHWARTZ-DENSITY` | `SchwartzMap.qfa_tendsto_cutoff and companion declarations` | direct | [QFALC005.Density](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LC005Density/QFALC005/Density.lean)|
| `M05-FOURIER-MULTIPLIERS` | `QFA.LC001SpectralReduction.gradient_fourier_distribution_eq and companion declarations` | direct | [QFALC001Reduction.DistributionMultipliers](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LC001SpectralReduction/QFALC001Reduction/DistributionMultipliers.lean)|
| `M06-FOURIER-NORM-ASSEMBLY` | `QFA.LC001SpectralReduction.FourierNormAEWitnesses and companion declarations` | conditional | [QFALC001Reduction.NativeFromAENorms](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LC001SpectralReduction/QFALC001Reduction/NativeFromAENorms.lean)|
| `M07-SPECTRAL-INTERPOLATION` | `QFA.Assembly.AnalyticChain.interpolation_of_nativeSpectralRealization and companion declarations` | conditional | [QFA.Assembly.AnalyticChain](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/LeanEndpoints/QFA/Assembly/AnalyticChain.lean)|
| `S02-SOBOLEV-HILBERT` | `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner and companion declarations` | direct | [Mathlib.Analysis.FunctionalSpaces.SobolevInequality](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean)|
| `S02-HOLDER` | `MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm and companion declarations` | domain-neutral | [Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean)|
| `S02-IBP-SCHWARTZ` | `SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left and companion declarations` | direct | [Mathlib.Analysis.Distribution.SchwartzSpace.Deriv](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Distribution/SchwartzSpace/Deriv.lean)|
| `S02-PLANCHEREL-L2` | `MeasureTheory.Lp.fourierTransformₗᵢ and companion declarations` | direct | [Mathlib.Analysis.Fourier.LpSpace](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Fourier/LpSpace.lean)|
| `S02-HESSIAN-PERIODIC` | `MethbokeAddon.WeakFouriermanB.physical_hessian_laplacian_eq` | periodic-model | [MethbokeAddon.WeakFouriermanB.PhysicalNonlinear](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/MethbokeAddon/WeakFouriermanB/PhysicalNonlinear.lean)|
| `S01-A-CONCRETE` | `Fefferman.ConcreteReal.RSpace and companion declarations` | direct | [ConcreteABCDUnifiedClosure](../../unpacked/FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0/ConcreteABCDUnifiedClosure.lean)|
| `S01-A-PORT` | `Fefferman.ConcreteReal.WholeSpaceZeroForceGlobalRegularity and companion declarations` | conditional | [ConcreteABCDUnifiedClosure](../../unpacked/FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0/ConcreteABCDUnifiedClosure.lean)|
| `M10-CORRECTED-QFA-ROOT` | `QFA.CorrectedPhysicalRoot.QUASI_FEFFERMAN_A_CORRECTED` | conditional | [QFACorrectedRoot.PhysicalRoot](https://github.com/randogelist/Methlib/blob/53b2318c2b586137b6db74c4d3a41bb0b964b2d8/Quasi-Fefferman-A/CorrectedPhysicalRoot/QFACorrectedRoot/PhysicalRoot.lean)|

## Passive Mathlib import/check text

This text has **not been executed**. It is suitable for a later authorized external cached compiler check after the source root and exact pin are selected. It introduces no theorem and no PDE assumption.

```lean
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.Sobolev
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

#check @MeasureTheory.Lp
#check @MeasureTheory.MemLp.toLp_eq_toLp_iff
#check @EuclideanSpace.real_norm_sq_eq
#check @MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner
#check @MeasureTheory.eLpNormLESNormFDerivOfEqInnerConst
#check @MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
#check @MeasureTheory.eLpNorm_norm_rpow
#check @SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left
#check @SchwartzMap.integral_bilinear_laplacian_right_eq_left
#check @ContDiffAt.isSymmSndFDerivAt
#check @SchwartzMap.fourier_lineDerivOp_eq
#check @MeasureTheory.Lp.fourierTransformₗᵢ
#check @MeasureTheory.Lp.norm_fourier_eq
#check @TemperedDistribution.memSobolev_iff_exists_smulLeftCLM_fourier
```

Optional native checks, after selecting the Methlib `LeanEndpoints` / LC004 / LC005 / LC001 package roots, are `QFA.Endpoints.Representation.complexifyL2LI`, `QFA.Endpoints.Representation.complexifyL2_weakDirectionalDerivative`, `QFA.Endpoints.Representation.CompactSchwartz.schwartzDerivativeWitnesses_of_compactSchwartz_unconditional`, `QFA.LC001SpectralReduction.gradient_fourier_ae`, `QFA.LC001SpectralReduction.laplacian_fourier_ae`, and `QFA.LC001SpectralReduction.nativeSpectralRealization_of_fourierNormAE`. Their exact module imports are in the JSON. Avoid overlaying the duplicate `QFA` module trees from `PhysicalRoot` and `LeanEndpoints`.
