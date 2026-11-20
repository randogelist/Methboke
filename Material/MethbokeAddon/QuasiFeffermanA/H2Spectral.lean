import MethbokeAddon.QuasiFeffermanA.PhysicalH2
import MethbokeAddon.QuasiFeffermanA.H1Spectral
import MethbokeAddon.QuasiFeffermanA.Spectral

/-!
# Fourier symmetry and exact physical H2 norms

The existing first-derivative Fourier theorem is applied twice to the actual
H2 graph. It proves equality of mixed weak derivatives and the full nine-term
Hessian density. Plancherel then proves the exact Hessian/Laplacian norm
identity and the inhomogeneous H2 norm formula. All integrability is obtained
from actual L2 fields; no spectral identity is an input premise.

Prepared source requires matching external compilation and independent named
type/axiom evidence. No local Lean, Lake or kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform

namespace MethbokeAddon.QuasiFeffermanA.H2Spectral

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open QFA.LC001SpectralReduction

private theorem second_multiplier_eq (a b : ℝ) :
    (((2 * Real.pi * Complex.I) * (b : ℂ)) *
      ((2 * Real.pi * Complex.I) * (a : ℂ))) =
        ((-((2 * Real.pi) ^ 2) * a * b : ℝ) : ℂ) := by
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  calc
    _ = (2 * (Real.pi : ℂ)) ^ 2 * (a : ℂ) * (b : ℂ) * Complex.I ^ 2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- The full ordered weak Hessian has the actual second-derivative Fourier
symbol, simultaneously for every pair of coordinate directions. -/
theorem spatialWeakHessian_fourier_ae
    {v : SpatialL2} {G : Fin 3 → SpatialL2} {H : Fin 3 → Fin 3 → SpatialL2}
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) :
    ∀ᵐ ξ : Space ∂volume, ∀ j k : Fin 3,
      (𝓕 (complexifyL2 (H j k)) : ComplexL2) ξ =
        (((-((2 * Real.pi) ^ 2) * ξ j * ξ k : ℝ) : ℂ)) •
          (𝓕 (complexifyL2 v) : ComplexL2) ξ := by
  have hrows : ∀ᵐ ξ : Space ∂volume, ∀ j k : Fin 3,
      (𝓕 (complexifyL2 (H j k)) : ComplexL2) ξ =
        ((2 * Real.pi * Complex.I) * (inner ℝ ξ (coordinateVector k) : ℂ)) •
          (𝓕 (complexifyL2 (G j)) : ComplexL2) ξ :=
    ae_all_iff.mpr (fun j : Fin 3 => H1Fourier.spatialWeakGradient_fourier_ae (hH j))
  filter_upwards [hrows, H1Fourier.spatialWeakGradient_fourier_ae hG] with ξ hξ hgξ
  intro j k
  have hc (a : Fin 3) : inner ℝ ξ (coordinateVector a) = ξ a := by
    simpa only [coordinateVector, EuclideanSpace.basisFun_apply] using
      EuclideanSpace.inner_basisFun_real (Fin 3) ξ a
  rw [hξ j k, hgξ j, hc k, hc j, smul_smul, second_multiplier_eq]

/-- Mixed weak derivatives agree as actual real L2 fields. No C2 representative
or symmetry hypothesis is required. -/
theorem spatialWeakHessian_symmetric
    {v : SpatialL2} {G : Fin 3 → SpatialL2} {H : Fin 3 → Fin 3 → SpatialL2}
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) (j k : Fin 3) :
    H j k = H k j := by
  apply complexifyL2LI.injective
  apply (Lp.fourierTransformₗᵢ Space ComplexVector).injective
  change (𝓕 (complexifyL2 (H j k)) : ComplexL2) = 𝓕 (complexifyL2 (H k j))
  apply Lp.ext
  filter_upwards [spatialWeakHessian_fourier_ae hG hH] with ξ hξ
  rw [hξ j k, hξ k j]
  have hc : -((2 * Real.pi) ^ 2) * ξ j * ξ k =
      -((2 * Real.pi) ^ 2) * ξ k * ξ j := by ring
  rw [hc]

/-- The sum over all nine physical second derivatives has exactly the
fourth-order radial density, with no component-count loss. -/
theorem spatialWeakHessian_fourier_norm_ae
    {v : SpatialL2} {G : Fin 3 → SpatialL2} {H : Fin 3 → Fin 3 → SpatialL2}
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) :
    (fun ξ : Space => ∑ j : Fin 3, ∑ k : Fin 3,
      ‖(𝓕 (complexifyL2 (H j k)) : ComplexL2) ξ‖ ^ 2) =ᵐ[volume]
        (fun ξ : Space => (2 * Real.pi) ^ 4 * ‖ξ‖ ^ 4 *
          ‖(𝓕 (complexifyL2 v) : ComplexL2) ξ‖ ^ 2) := by
  have hrows : ∀ᵐ ξ : Space ∂volume, ∀ j : Fin 3,
      (∑ k : Fin 3, ‖(𝓕 (complexifyL2 (H j k)) : ComplexL2) ξ‖ ^ 2) =
        (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
          ‖(𝓕 (complexifyL2 (G j)) : ComplexL2) ξ‖ ^ 2 :=
    ae_all_iff.mpr (fun j : Fin 3 =>
      H1Spectral.spatialWeakGradient_fourier_norm_ae (hH j))
  filter_upwards [hrows, H1Spectral.spatialWeakGradient_fourier_norm_ae hG] with ξ hξ hgξ
  calc
    (∑ j : Fin 3, ∑ k : Fin 3,
        ‖(𝓕 (complexifyL2 (H j k)) : ComplexL2) ξ‖ ^ 2) =
        ∑ j : Fin 3, (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
          ‖(𝓕 (complexifyL2 (G j)) : ComplexL2) ξ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact hξ j
    _ = (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
        (∑ j : Fin 3, ‖(𝓕 (complexifyL2 (G j)) : ComplexL2) ξ‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ = _ := by rw [hgξ]; ring

theorem physicalH2_hessian_fourier_ae (u : PhysicalH2) :
    ∀ᵐ ξ : Space ∂volume, ∀ j k : Fin 3,
      (𝓕 (complexifyL2 (physicalH2Hessian j k u)) : ComplexL2) ξ =
        (((-((2 * Real.pi) ^ 2) * ξ j * ξ k : ℝ) : ℂ)) •
          (𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ :=
  spatialWeakHessian_fourier_ae (physicalH2_weakGradient u) (physicalH2_weakHessian u)

theorem physicalH2_hessian_symmetric (u : PhysicalH2) (j k : Fin 3) :
    physicalH2Hessian j k u = physicalH2Hessian k j u :=
  spatialWeakHessian_symmetric (physicalH2_weakGradient u) (physicalH2_weakHessian u) j k

theorem physicalH2_laplacian_fourier_ae (u : PhysicalH2) :
    (fun ξ : Space => (𝓕 (complexifyL2 (physicalH2Laplacian u)) : ComplexL2) ξ)
      =ᵐ[volume] (fun ξ : Space =>
        ((-((2 * Real.pi) ^ 2) : ℂ) * (‖ξ‖ ^ 2 : ℂ)) •
          (𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ) :=
  FourierMultipliers.laplacian_fourier_ae (physicalH2_schwartzDerivativeWitnesses u)

theorem physicalH2_fourier_laplacian_integrable (u : PhysicalH2) :
    Integrable (fun ξ : Space => (2 * Real.pi) ^ 4 * ‖ξ‖ ^ 4 *
      ‖(𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ‖ ^ 2) volume :=
  (nativeSpectralRealization_of_schwartzDerivativeWitnesses
    (physicalH2_schwartzDerivativeWitnesses u)).laplacian_integrable

theorem physicalH2_laplacian_norm_sq_eq_fourier (u : PhysicalH2) :
    ‖physicalH2Laplacian u‖ ^ 2 =
      ∫ ξ : Space, (2 * Real.pi) ^ 4 * ‖ξ‖ ^ 4 *
        ‖(𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ‖ ^ 2 := by
  simpa only [QFA.Endpoints.Agmon.laplacianEnergy, complexifyL2_norm] using
    (nativeSpectralRealization_of_schwartzDerivativeWitnesses
      (physicalH2_schwartzDerivativeWitnesses u)).laplacian_identity

private theorem integral_hessian_fourier_sum (H : Fin 3 → Fin 3 → SpatialL2) :
    (∫ ξ : Space, ∑ j : Fin 3, ∑ k : Fin 3,
      ‖(𝓕 (complexifyL2 (H j k)) : ComplexL2) ξ‖ ^ 2) =
        ∑ j : Fin 3, ∑ k : Fin 3, ‖H j k‖ ^ 2 := by
  calc
    (∫ ξ : Space, ∑ j : Fin 3, ∑ k : Fin 3,
        ‖(𝓕 (complexifyL2 (H j k)) : ComplexL2) ξ‖ ^ 2) =
        ∑ j : Fin 3, ∫ ξ : Space, ∑ k : Fin 3,
          ‖(𝓕 (complexifyL2 (H j k)) : ComplexL2) ξ‖ ^ 2 := by
      simpa using integral_finsetSum Finset.univ (fun j _ =>
        integrable_gradient_fourier_sum (fun k => complexifyL2 (H j k)))
    _ = ∑ j : Fin 3, ∑ k : Fin 3, ‖H j k‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_gradient_fourier_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Lp.norm_fourier_eq, complexifyL2_norm]

/-- The actual L2 Hessian and Laplacian have exactly the same squared norm. -/
theorem physicalH2_hessian_norm_sq_eq_laplacian (u : PhysicalH2) :
    (∑ j : Fin 3, ∑ k : Fin 3, ‖physicalH2Hessian j k u‖ ^ 2) =
      ‖physicalH2Laplacian u‖ ^ 2 := by
  calc
    (∑ j : Fin 3, ∑ k : Fin 3, ‖physicalH2Hessian j k u‖ ^ 2) =
        ∫ ξ : Space, ∑ j : Fin 3, ∑ k : Fin 3,
          ‖(𝓕 (complexifyL2 (physicalH2Hessian j k u)) : ComplexL2) ξ‖ ^ 2 :=
      (integral_hessian_fourier_sum (fun j k => physicalH2Hessian j k u)).symm
    _ = ∫ ξ : Space, (2 * Real.pi) ^ 4 * ‖ξ‖ ^ 4 *
        ‖(𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ‖ ^ 2 :=
      integral_congr_ae (spatialWeakHessian_fourier_norm_ae
        (physicalH2_weakGradient u) (physicalH2_weakHessian u))
    _ = ‖physicalH2Laplacian u‖ ^ 2 :=
      (physicalH2_laplacian_norm_sq_eq_fourier u).symm

theorem physicalH2_norm_sq_eq_laplacian (u : PhysicalH2) :
    ‖u‖ ^ 2 = ‖physicalH2Velocity u‖ ^ 2 +
      (∑ j : Fin 3, ‖physicalH2Gradient j u‖ ^ 2) + ‖physicalH2Laplacian u‖ ^ 2 := by
  rw [physicalH2_norm_sq, physicalH2_hessian_norm_sq_eq_laplacian]

theorem physicalH2_weighted_fourier_integrable (u : PhysicalH2) :
    Integrable (fun ξ : Space => ‖ξ‖ ^ 4 *
      ‖(𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ‖ ^ 2) volume := by
  have h := (physicalH2_fourier_laplacian_integrable u).const_mul ((2 * Real.pi) ^ 4)⁻¹
  have hpi : (2 * Real.pi) ^ 4 ≠ 0 := by positivity
  simpa only [← mul_assoc, inv_mul_cancel₀ hpi, one_mul] using h

theorem physicalH2_laplacian_eq_fourier_weighted (u : PhysicalH2) :
    ‖physicalH2Laplacian u‖ ^ 2 = (2 * Real.pi) ^ 4 *
      (∫ ξ : Space, ‖ξ‖ ^ 4 *
        ‖(𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ‖ ^ 2) := by
  rw [physicalH2_laplacian_norm_sq_eq_fourier, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  ring

theorem physicalH2_norm_sq_eq_fourier (u : PhysicalH2) :
    ‖u‖ ^ 2 =
      (∫ ξ : Space, ‖(𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ‖ ^ 2) +
      (4 * Real.pi ^ 2) * (∫ ξ : Space, ‖ξ‖ ^ 2 *
        ‖(𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ‖ ^ 2) +
      (2 * Real.pi) ^ 4 * (∫ ξ : Space, ‖ξ‖ ^ 4 *
        ‖(𝓕 (complexifyL2 (physicalH2Velocity u)) : ComplexL2) ξ‖ ^ 2) := by
  rw [physicalH2_norm_sq_eq_laplacian,
    ← H1Spectral.integral_fourier_energy (physicalH2Velocity u),
    ← H1Spectral.four_pi_sq_mul_integral_weighted (physicalH2_weakGradient u),
    physicalH2_laplacian_eq_fourier_weighted]

end MethbokeAddon.QuasiFeffermanA.H2Spectral
