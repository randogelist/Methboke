import MethbokeAddon.QuasiFeffermanA.H2Spectral
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Physical integration by parts and the Laplacian energy pairing

The native compact-test weak derivatives determine the first-order Fourier
symbols. Complex Plancherel and the skew-adjointness of those imaginary
symbols prove integration by parts for arbitrary actual physical H1 fields.
Applying that result to each actual H2 gradient gives the H1-H2 Green
identity, the real L2 symmetry of the physical Laplacian, and its exact
negative-enstrophy pairing. The L2 inner products are genuine integrals:
their integrability is supplied by the native L2 inner-product construction.

There is no boundary, spectral-pairing, integration-by-parts or regularity
witness among the hypotheses. This spatial layer makes no forced heat or
Navier-Stokes existence claim.

Prepared source requires matching external compilation and independent
named type/axiom evidence. No local Lean, Lake or kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform

namespace MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation

private theorem real_inner_complexify (u v : SpatialL2) :
    inner ℝ u v = Complex.re (inner ℂ (complexifyL2 u) (complexifyL2 v)) := by
  letI : InnerProductSpace ℝ ComplexL2 := InnerProductSpace.rclikeToReal ℂ ComplexL2
  exact (complexifyL2LI.inner_map_map u v).symm

private theorem complexify_inner_eq_fourier (u v : SpatialL2) :
    inner ℂ (complexifyL2 u) (complexifyL2 v) =
      ∫ ξ : Space, inner ℂ ((𝓕 (complexifyL2 u) : ComplexL2) ξ)
        ((𝓕 (complexifyL2 v) : ComplexL2) ξ) := by
  rw [← Lp.inner_fourier_eq, L2.inner_def]

private theorem first_symbol_skew_inner (b : ℝ) (x y : ComplexVector) :
    inner ℂ x (((2 * Real.pi * Complex.I) * (b : ℂ)) • y) =
      -inner ℂ (((2 * Real.pi * Complex.I) * (b : ℂ)) • x) y := by
  have hc : starRingEnd ℂ ((2 * Real.pi * Complex.I) * (b : ℂ)) =
      -((2 * Real.pi * Complex.I) * (b : ℂ)) := by
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [inner_smul_right, inner_smul_left, hc, neg_mul, neg_neg]

/-- Genuine first-order integration by parts for two actual physical H1
fields on the original full spatial volume. -/
theorem physicalH1_gradient_integration_by_parts
    (u v : PhysicalH1) (j : Fin 3) :
    inner ℝ (physicalH1Velocity u) (physicalH1Gradient j v) =
      -inner ℝ (physicalH1Gradient j u) (physicalH1Velocity v) := by
  have hc :
      inner ℂ (complexifyL2 (physicalH1Velocity u))
          (complexifyL2 (physicalH1Gradient j v)) =
        -inner ℂ (complexifyL2 (physicalH1Gradient j u))
          (complexifyL2 (physicalH1Velocity v)) := by
    rw [complexify_inner_eq_fourier, complexify_inner_eq_fourier, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [H1Fourier.spatialWeakGradient_fourier_ae (physicalH1_weakGradient u),
      H1Fourier.spatialWeakGradient_fourier_ae (physicalH1_weakGradient v)] with ξ hu hv
    rw [hu j, hv j]
    exact first_symbol_skew_inner (inner ℝ ξ (coordinateVector j)) _ _
  rw [real_inner_complexify, real_inner_complexify]
  simpa only [Complex.neg_re] using congrArg Complex.re hc

/-- The actual Laplacian pairs against any physical H1 field as minus the
literal sum of the three actual weak-gradient inner products. -/
theorem physicalH1H2_laplacian_pairing (u : PhysicalH1) (v : PhysicalH2) :
    inner ℝ (physicalH1Velocity u) (physicalH2Laplacian v) =
      -(∑ j : Fin 3, inner ℝ (physicalH1Gradient j u) (physicalH2Gradient j v)) := by
  rw [physicalH2Laplacian_apply, inner_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [physicalH2GradientH1_velocity, physicalH2GradientH1_gradient] using
    physicalH1_gradient_integration_by_parts u (physicalH2GradientH1 j v) j

/-- Real L2 symmetry on the actual physical H2 graph. This is the explicit
bilinear pairing identity, without asserting an unbounded-operator domain theorem. -/
theorem physicalH2_laplacian_symmetric (u v : PhysicalH2) :
    inner ℝ (physicalH2Laplacian u) (physicalH2Velocity v) =
      inner ℝ (physicalH2Velocity u) (physicalH2Laplacian v) := by
  calc
    inner ℝ (physicalH2Laplacian u) (physicalH2Velocity v) =
        inner ℝ (physicalH2Velocity v) (physicalH2Laplacian u) :=
      real_inner_comm _ _
    _ = -(∑ j : Fin 3, inner ℝ (physicalH2Gradient j v) (physicalH2Gradient j u)) := by
      simpa only [physicalH2ToH1_velocity, physicalH2ToH1_gradient] using
        physicalH1H2_laplacian_pairing (physicalH2ToH1 v) u
    _ = -(∑ j : Fin 3, inner ℝ (physicalH2Gradient j u) (physicalH2Gradient j v)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact real_inner_comm _ _
    _ = inner ℝ (physicalH2Velocity u) (physicalH2Laplacian v) := by
      symm
      simpa only [physicalH2ToH1_velocity, physicalH2ToH1_gradient] using
        physicalH1H2_laplacian_pairing (physicalH2ToH1 u) v

/-- The Laplacian of every actual physical H2 field has exactly the negative
physical H1 enstrophy pairing, with no one-half normalization. -/
theorem physicalH2_laplacian_enstrophy (u : PhysicalH2) :
    inner ℝ (physicalH2Velocity u) (physicalH2Laplacian u) =
      -physicalH1Enstrophy (physicalH2ToH1 u) := by
  simpa only [physicalH1Enstrophy, physicalH2ToH1_velocity, physicalH2ToH1_gradient,
    real_inner_self_eq_norm_sq] using
    physicalH1H2_laplacian_pairing (physicalH2ToH1 u) u

end MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy
