import MethbokeAddon.QuasiFeffermanA.H1Fourier
import MethbokeAddon.QuasiFeffermanA.PhysicalH1Budget
import QFALC001Reduction.NativeFromAENorms
import Mathlib.Analysis.Complex.Norm

/-!
# H1-only physical Fourier energy and enstrophy

The actual compact-test first derivatives determine the weighted Fourier
density, its genuine integrability and the exact physical energy identities.
Only the supplied velocity and first derivatives in L2 are required. There is
no Laplacian/H2 witness, assumed spectral norm identity, or temporal premise.

The factor 4*pi^2 is retained. The extended nonnegative integral identities
are obtained after proving integrability, not by totalization. Physical H1
sector outputs may use these theorems once independently constructed.

Prepared source requires matching cached external compiler and named audits.
No local Lean/Lake/kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform ENNReal

namespace MethbokeAddon.QuasiFeffermanA.H1Spectral

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open QFA.LC001SpectralReduction

private theorem gradient_multiplier_norm_sq (b : ℝ) (z : ComplexVector) :
    ‖((2 * Real.pi * Complex.I) * (b : ℂ)) • z‖ ^ 2 =
      (2 * Real.pi) ^ 2 * b ^ 2 * ‖z‖ ^ 2 := by
  have h (a : ℝ) :
      ‖(((a : ℂ) * Complex.I) * (b : ℂ)) • z‖ ^ 2 =
        a ^ 2 * b ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_smul, mul_pow, Complex.sq_norm]
    simp only [Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_I, one_mul, pow_two, mul_assoc]
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using h (2 * Real.pi)

/-- The literal first-derivative density identity follows from the native
physical weak gradient, with no higher-derivative premise. -/
theorem spatialWeakGradient_fourier_norm_ae
    {u : SpatialL2} {G : Fin 3 → SpatialL2}
    (hweak : SpatialWeakGradient u G) :
    (fun ξ : Space => ∑ j : Fin 3, ‖(𝓕 (complexifyL2 (G j)) : ComplexL2) ξ‖ ^ 2)
      =ᵐ[volume] (fun ξ : Space =>
        (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) := by
  filter_upwards [H1Fourier.spatialWeakGradient_fourier_ae hweak] with ξ hξ
  calc
    (∑ j : Fin 3, ‖(𝓕 (complexifyL2 (G j)) : ComplexL2) ξ‖ ^ 2) =
        ∑ j : Fin 3, (2 * Real.pi) ^ 2 * (ξ j) ^ 2 *
          ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hξ j]
      have hc : inner ℝ ξ (coordinateVector j) = ξ j := by
        simpa only [coordinateVector, EuclideanSpace.basisFun_apply] using
          EuclideanSpace.inner_basisFun_real (Fin 3) ξ j
      rw [hc]
      exact gradient_multiplier_norm_sq (ξ j) ((𝓕 (complexifyL2 u) : ComplexL2) ξ)
    _ = (2 * Real.pi) ^ 2 * (∑ j : Fin 3, (ξ j) ^ 2) *
        ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2 := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = _ := by rw [← EuclideanSpace.real_norm_sq_eq ξ]

theorem integrable_fourier_energy (u : SpatialL2) :
    Integrable (fun ξ : Space => ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) volume :=
  integrable_norm_sq (𝓕 (complexifyL2 u) : ComplexL2)

/-- Full-volume Plancherel and actual real complexification identify energy. -/
theorem integral_fourier_energy (u : SpatialL2) :
    (∫ ξ : Space, ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) = ‖u‖ ^ 2 := by
  rw [integral_norm_sq_eq_norm_sq, Lp.norm_fourier_eq, complexifyL2_norm]

/-- Weighted integrability is proved from actual first derivatives in L2. -/
theorem integrable_fourier_gradient
    {u : SpatialL2} {G : Fin 3 → SpatialL2}
    (hweak : SpatialWeakGradient u G) :
    Integrable (fun ξ : Space =>
      (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) volume :=
  (integrable_gradient_fourier_sum (fun j => complexifyL2 (G j))).congr
    (spatialWeakGradient_fourier_norm_ae hweak)

/-- The exact squared-gradient norm equals its native Fourier integral. -/
theorem integral_fourier_gradient
    {u : SpatialL2} {G : Fin 3 → SpatialL2}
    (hweak : SpatialWeakGradient u G) :
    (∫ ξ : Space, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
      ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) =
        ∑ j : Fin 3, ‖G j‖ ^ 2 := by
  calc
    (∫ ξ : Space, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
        ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) =
        ∫ ξ : Space, ∑ j : Fin 3, ‖(𝓕 (complexifyL2 (G j)) : ComplexL2) ξ‖ ^ 2 :=
      integral_congr_ae (spatialWeakGradient_fourier_norm_ae hweak).symm
    _ = ∑ j : Fin 3, ‖(𝓕 (complexifyL2 (G j)) : ComplexL2)‖ ^ 2 :=
      integral_gradient_fourier_sum (fun j => complexifyL2 (G j))
    _ = ∑ j : Fin 3, ‖G j‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Lp.norm_fourier_eq, complexifyL2_norm]

/-- The unnormalized weighted density is genuinely integrable as well. -/
theorem integrable_fourier_weighted
    {u : SpatialL2} {G : Fin 3 → SpatialL2}
    (hweak : SpatialWeakGradient u G) :
    Integrable (fun ξ : Space =>
      ‖ξ‖ ^ 2 * ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) volume := by
  have h := (integrable_fourier_gradient hweak).const_mul ((2 * Real.pi) ^ 2)⁻¹
  have hpi : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  simpa only [← mul_assoc, inv_mul_cancel₀ hpi, one_mul] using h

/-- The physical factor is exactly four times pi squared. -/
theorem four_pi_sq_mul_integral_weighted
    {u : SpatialL2} {G : Fin 3 → SpatialL2}
    (hweak : SpatialWeakGradient u G) :
    (4 * Real.pi ^ 2) * (∫ ξ : Space,
      ‖ξ‖ ^ 2 * ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) =
        ∑ j : Fin 3, ‖G j‖ ^ 2 := by
  calc
    (4 * Real.pi ^ 2) * (∫ ξ : Space,
        ‖ξ‖ ^ 2 * ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) =
        ∫ ξ : Space, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
          ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ξ
      ring
    _ = _ := integral_fourier_gradient hweak

theorem physicalH1_fourier_enstrophy_integrable (u : PhysicalH1) :
    Integrable (fun ξ : Space => ‖ξ‖ ^ 2 *
      ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) volume :=
  integrable_fourier_weighted (physicalH1_weakGradient u)

theorem physicalH1_energy_eq_fourier (u : PhysicalH1) :
    physicalH1Energy u =
      ∫ ξ : Space, ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2 :=
  (integral_fourier_energy (physicalH1Velocity u)).symm

theorem physicalH1_enstrophy_eq_fourier (u : PhysicalH1) :
    physicalH1Enstrophy u = (4 * Real.pi ^ 2) *
      (∫ ξ : Space, ‖ξ‖ ^ 2 *
        ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) :=
  (four_pi_sq_mul_integral_weighted (physicalH1_weakGradient u)).symm

/-- The actual complete inhomogeneous H1 norm retains both low and high
frequencies. No Poincare estimate or homogeneous completion is substituted. -/
theorem physicalH1_norm_sq_eq_fourier (u : PhysicalH1) :
    ‖u‖ ^ 2 =
      (∫ ξ : Space, ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) +
        (4 * Real.pi ^ 2) * (∫ ξ : Space, ‖ξ‖ ^ 2 *
          ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) := by
  rw [physicalH1_norm_sq_eq_energy_add_enstrophy,
    physicalH1_energy_eq_fourier, physicalH1_enstrophy_eq_fourier]

/-- Nonnegative extended Fourier integration agrees with the genuine finite
weighted integral. This makes the finiteness claim explicit. -/
theorem physicalH1_weighted_lintegral_eq (u : PhysicalH1) :
    (∫⁻ ξ : Space, ENNReal.ofReal (‖ξ‖ ^ 2 *
      ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2)) =
        ENNReal.ofReal (∫ ξ : Space, ‖ξ‖ ^ 2 *
          ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) := by
  exact (ofReal_integral_eq_lintegral_ofReal
    (physicalH1_fourier_enstrophy_integrable u)
    (Filter.Eventually.of_forall (fun ξ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))).symm

theorem physicalH1_weighted_lintegral_finite (u : PhysicalH1) :
    (∫⁻ ξ : Space, ENNReal.ofReal (‖ξ‖ ^ 2 *
      ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2)) ≠ ∞ := by
  rw [physicalH1_weighted_lintegral_eq]
  exact ENNReal.ofReal_ne_top

end MethbokeAddon.QuasiFeffermanA.H1Spectral
