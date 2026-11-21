import R3EhrenfestBandlimited.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform ContDiff NNReal

namespace R3EhrenfestBandlimited.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.RealFourier
open MethbokeAddon.R3Ehrenfest.SharpCutoff
open MethbokeAddon.R3Ehrenfest.Bandlimited
open QFA.Endpoints.Representation
open QFA.Endpoints.Agmon (ComplexVector ComplexL2)

-- Literal whole-space carriers and measure, independent of the new aliases.
example : Space = EuclideanSpace ℝ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl

-- The explicit bound and actual real-linear first derivative operator.
example (n : ℕ) :
    cutoffDerivativeBound n = 2 * Real.pi * ((n : ℝ) + 1) := rfl
example (n : ℕ) : 0 < cutoffDerivativeBound n := cutoffDerivativeBound_pos n
example (n : ℕ) (j : Fin 3) : SpatialL2 →L[ℝ] SpatialL2 := cutoffDerivative n j
example (n : ℕ) (j : Fin 3) (u : SpatialL2) :
    (fun ξ : Space =>
      (𝓕 (complexifyL2 (cutoffDerivative n j u)) : ComplexL2) ξ)
      =ᵐ[volume] (fun ξ : Space =>
        ((2 * Real.pi * Complex.I) *
          (inner ℝ ξ (EuclideanSpace.single j (1 : ℝ)) : ℂ)) •
            (𝓕 (complexifyL2 (sharpCutoff n u)) : ComplexL2) ξ) :=
  cutoffDerivative_fourier_ae n j u
example (n : ℕ) (j : Fin 3) (u : SpatialL2) :
    ‖cutoffDerivative n j u‖ ≤
      (2 * Real.pi * ((n : ℝ) + 1)) * ‖u‖ := norm_cutoffDerivative_le n j u
example (n : ℕ) (j : Fin 3) (u : SpatialL2) :
    sharpCutoff n (cutoffDerivative n j u) = cutoffDerivative n j u :=
  sharpCutoff_cutoffDerivative n j u

-- Actual compact-test weak derivatives are conclusions for every L2 input.
example (n : ℕ) (u : SpatialL2) :
    ∀ (j : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) •
        sharpCutoff n u x) =
          -(∫ x : Space, ψ x • cutoffDerivative n j u x) :=
  spatialWeakGradient_sharpCutoff_constructed n u
example (n : ℕ) (u : SpatialL2) (G : Fin 3 → SpatialL2)
    (hG : SpatialWeakGradient u G) (j : Fin 3) :
    cutoffDerivative n j u = sharpCutoff n (G j) :=
  cutoffDerivative_eq_sharpCutoff_of_weakGradient n hG j
example (n : ℕ) (j : Fin 3) (u : SpatialL2) :
    cutoffDerivative n j (sharpCutoff n u) = cutoffDerivative n j u :=
  cutoffDerivative_sharpCutoff n j u

-- The second derivatives are also constructed; no Hessian witness is supplied.
example (n : ℕ) (u : SpatialL2) :
    ∀ (j k : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single k (1 : ℝ)) •
        cutoffDerivative n j u x) =
          -(∫ x : Space, ψ x • cutoffDerivative n k (cutoffDerivative n j u) x) :=
  spatialWeakHessian_sharpCutoff_constructed n u
example (n : ℕ) (u : SpatialL2) : PhysicalH2 := sharpCutoffH2 n u
example (n : ℕ) (u : SpatialL2) :
    physicalH2Velocity (sharpCutoffH2 n u) = sharpCutoff n u :=
  sharpCutoffH2_velocity n u
example (n : ℕ) (u : SpatialL2) (j : Fin 3) :
    physicalH2Gradient j (sharpCutoffH2 n u) = cutoffDerivative n j u :=
  sharpCutoffH2_gradient n u j
example (n : ℕ) (u : SpatialL2) (j k : Fin 3) :
    physicalH2Hessian j k (sharpCutoffH2 n u) =
      cutoffDerivative n k (cutoffDerivative n j u) :=
  sharpCutoffH2_hessian n u j k

-- Explicit nonsharp graph norm bound; n-dependence is part of the contract.
example (n : ℕ) (u : SpatialL2) :
    ‖sharpCutoffH2 n u‖ ^ 2 ≤
      (1 + 3 * (cutoffDerivativeBound n) ^ 2 +
        9 * (cutoffDerivativeBound n) ^ 4) * ‖u‖ ^ 2 :=
  sharpCutoffH2_norm_sq_le n u
example (n : ℕ) :
    sharpCutoffH2Bound n =
      Real.sqrt (1 + 3 * (cutoffDerivativeBound n) ^ 2 +
        9 * (cutoffDerivativeBound n) ^ 4) := rfl
example (n : ℕ) (u : SpatialL2) :
    ‖sharpCutoffH2 n u‖ ≤ sharpCutoffH2Bound n * ‖u‖ :=
  norm_sharpCutoffH2_le n u
example (n : ℕ) : SpatialL2 →L[ℝ] PhysicalH2 := sharpCutoffH2CLM n
example (n : ℕ) (u : SpatialL2) :
    sharpCutoffH2CLM n u = sharpCutoffH2 n u := sharpCutoffH2CLM_apply n u

-- Compatibility is with the existing native graphs and actual cutoff.
example (n : ℕ) (u : PhysicalH1) :
    physicalH2ToH1 (sharpCutoffH2 n (physicalH1Velocity u)) =
      physicalH1SharpCutoff n u := sharpCutoffH2_toH1 n u
example (n : ℕ) (u : PhysicalH2)
    (hu : sharpCutoff n (physicalH2Velocity u) = physicalH2Velocity u) :
    sharpCutoffH2 n (physicalH2Velocity u) = u := sharpCutoffH2_eq_of_fixed n u hu

end R3EhrenfestBandlimited.ExpectedTypes

-- Ordered exact-type and named axiom reports, executed only by authorized external CI.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivativeBound"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivativeBound
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivativeBound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivativeBound"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivativeBound
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivativeBound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivativeBound_pos"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivativeBound_pos
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivativeBound_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivativeBound_pos"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivativeBound_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivativeBound_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_fourier_ae"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_fourier_ae"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.norm_cutoffDerivative_le"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.norm_cutoffDerivative_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.norm_cutoffDerivative_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.norm_cutoffDerivative_le"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.norm_cutoffDerivative_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.norm_cutoffDerivative_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoff_cutoffDerivative"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoff_cutoffDerivative
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoff_cutoffDerivative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoff_cutoffDerivative"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoff_cutoffDerivative
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoff_cutoffDerivative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.spatialWeakGradient_sharpCutoff_constructed"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.spatialWeakGradient_sharpCutoff_constructed
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.spatialWeakGradient_sharpCutoff_constructed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.spatialWeakGradient_sharpCutoff_constructed"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.spatialWeakGradient_sharpCutoff_constructed
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.spatialWeakGradient_sharpCutoff_constructed"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_eq_sharpCutoff_of_weakGradient"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_eq_sharpCutoff_of_weakGradient
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_eq_sharpCutoff_of_weakGradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_eq_sharpCutoff_of_weakGradient"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_eq_sharpCutoff_of_weakGradient
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_eq_sharpCutoff_of_weakGradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_sharpCutoff"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_sharpCutoff
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_sharpCutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_sharpCutoff"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_sharpCutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.cutoffDerivative_sharpCutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.spatialWeakHessian_sharpCutoff_constructed"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.spatialWeakHessian_sharpCutoff_constructed
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.spatialWeakHessian_sharpCutoff_constructed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.spatialWeakHessian_sharpCutoff_constructed"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.spatialWeakHessian_sharpCutoff_constructed
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.spatialWeakHessian_sharpCutoff_constructed"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_velocity"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_velocity
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_velocity"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_gradient"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_gradient
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_gradient"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_hessian"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_hessian
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_hessian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_hessian"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_hessian
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_hessian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_norm_sq_le"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_norm_sq_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_norm_sq_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_norm_sq_le"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_norm_sq_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_norm_sq_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2Bound"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2Bound
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2Bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2Bound"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2Bound
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2Bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.norm_sharpCutoffH2_le"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.norm_sharpCutoffH2_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.norm_sharpCutoffH2_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.norm_sharpCutoffH2_le"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.norm_sharpCutoffH2_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.norm_sharpCutoffH2_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2CLM"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2CLM
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2CLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2CLM"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2CLM
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2CLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2CLM_apply"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2CLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2CLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2CLM_apply"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2CLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2CLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_toH1"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_toH1
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_toH1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_toH1"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_toH1
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_toH1"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_eq_of_fixed"
#check @MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_eq_of_fixed
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_eq_of_fixed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_eq_of_fixed"
#print axioms MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_eq_of_fixed
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Bandlimited.sharpCutoffH2_eq_of_fixed"

