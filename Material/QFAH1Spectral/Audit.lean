import QFAH1Spectral.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform ENNReal ContDiff

namespace QFAH1Spectral.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.H1Spectral
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation

-- Independent literal carrier and physical derivative contracts.
example : MethbokeAddon.QuasiFeffermanA.Space = EuclideanSpace ℝ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl

example (u : SpatialL2) (G : Fin 3 → SpatialL2) :
    SpatialWeakGradient u G ↔
      ∀ (j : Fin 3) (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ),
        ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ x : MethbokeAddon.QuasiFeffermanA.Space,
          fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) • u x) =
            -(∫ x : MethbokeAddon.QuasiFeffermanA.Space, ψ x • G j x) := Iff.rfl

example (u : PhysicalH1) : physicalH1Energy u = ‖physicalH1Velocity u‖ ^ 2 := rfl
example (u : PhysicalH1) : physicalH1Enstrophy u =
    ∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2 := rfl

-- No Laplacian, H2, weighted integrability or spectral identity premise.
example (u : SpatialL2) (G : Fin 3 → SpatialL2)
    (h : SpatialWeakGradient u G) :
    (fun ξ : MethbokeAddon.QuasiFeffermanA.Space =>
      ∑ j : Fin 3, ‖(𝓕 (complexifyL2 (G j)) : ComplexL2) ξ‖ ^ 2) =ᵐ[volume]
      (fun ξ : MethbokeAddon.QuasiFeffermanA.Space =>
        (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) :=
  spatialWeakGradient_fourier_norm_ae h

example (u : SpatialL2) :
    Integrable (fun ξ : MethbokeAddon.QuasiFeffermanA.Space =>
      ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) volume :=
  integrable_fourier_energy u

example (u : SpatialL2) :
    (∫ ξ : MethbokeAddon.QuasiFeffermanA.Space,
      ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) = ‖u‖ ^ 2 :=
  integral_fourier_energy u

example (u : SpatialL2) (G : Fin 3 → SpatialL2)
    (h : SpatialWeakGradient u G) :
    Integrable (fun ξ : MethbokeAddon.QuasiFeffermanA.Space =>
      (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) volume :=
  integrable_fourier_gradient h

example (u : SpatialL2) (G : Fin 3 → SpatialL2)
    (h : SpatialWeakGradient u G) :
    (∫ ξ : MethbokeAddon.QuasiFeffermanA.Space,
      (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 * ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) =
        ∑ j : Fin 3, ‖G j‖ ^ 2 := integral_fourier_gradient h

example (u : SpatialL2) (G : Fin 3 → SpatialL2)
    (h : SpatialWeakGradient u G) :
    Integrable (fun ξ : MethbokeAddon.QuasiFeffermanA.Space =>
      ‖ξ‖ ^ 2 * ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) volume :=
  integrable_fourier_weighted h

example (u : SpatialL2) (G : Fin 3 → SpatialL2)
    (h : SpatialWeakGradient u G) :
    (4 * Real.pi ^ 2) * (∫ ξ : MethbokeAddon.QuasiFeffermanA.Space,
      ‖ξ‖ ^ 2 * ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) =
        ∑ j : Fin 3, ‖G j‖ ^ 2 := four_pi_sq_mul_integral_weighted h

example (u : PhysicalH1) :
    Integrable (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => ‖ξ‖ ^ 2 *
      ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) volume :=
  physicalH1_fourier_enstrophy_integrable u

example (u : PhysicalH1) :
    ‖physicalH1Velocity u‖ ^ 2 =
      ∫ ξ : MethbokeAddon.QuasiFeffermanA.Space,
        ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2 :=
  physicalH1_energy_eq_fourier u

example (u : PhysicalH1) :
    (∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2) = (4 * Real.pi ^ 2) *
      (∫ ξ : MethbokeAddon.QuasiFeffermanA.Space, ‖ξ‖ ^ 2 *
        ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) :=
  physicalH1_enstrophy_eq_fourier u

example (u : PhysicalH1) :
    ‖u‖ ^ 2 = (∫ ξ : MethbokeAddon.QuasiFeffermanA.Space,
      ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) +
        (4 * Real.pi ^ 2) * (∫ ξ : MethbokeAddon.QuasiFeffermanA.Space, ‖ξ‖ ^ 2 *
          ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) :=
  physicalH1_norm_sq_eq_fourier u

example (u : PhysicalH1) :
    (∫⁻ ξ : MethbokeAddon.QuasiFeffermanA.Space, ENNReal.ofReal (‖ξ‖ ^ 2 *
      ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2)) =
        ENNReal.ofReal (∫ ξ : MethbokeAddon.QuasiFeffermanA.Space, ‖ξ‖ ^ 2 *
          ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) :=
  physicalH1_weighted_lintegral_eq u

example (u : PhysicalH1) :
    (∫⁻ ξ : MethbokeAddon.QuasiFeffermanA.Space, ENNReal.ofReal (‖ξ‖ ^ 2 *
      ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2)) ≠ ∞ :=
  physicalH1_weighted_lintegral_finite u

end QFAH1Spectral.ExpectedTypes

-- BEGIN NAMED REPORTS

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.spatialWeakGradient_fourier_norm_ae"
#check @MethbokeAddon.QuasiFeffermanA.H1Spectral.spatialWeakGradient_fourier_norm_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.spatialWeakGradient_fourier_norm_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.spatialWeakGradient_fourier_norm_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Spectral.spatialWeakGradient_fourier_norm_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.spatialWeakGradient_fourier_norm_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_energy"
#check @MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_energy
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_energy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_energy"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_energy
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_energy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.integral_fourier_energy"
#check @MethbokeAddon.QuasiFeffermanA.H1Spectral.integral_fourier_energy
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.integral_fourier_energy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.integral_fourier_energy"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Spectral.integral_fourier_energy
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.integral_fourier_energy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_gradient"
#check @MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.integral_fourier_gradient"
#check @MethbokeAddon.QuasiFeffermanA.H1Spectral.integral_fourier_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.integral_fourier_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.integral_fourier_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Spectral.integral_fourier_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.integral_fourier_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_weighted"
#check @MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_weighted
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_weighted"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_weighted"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_weighted
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.integrable_fourier_weighted"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.four_pi_sq_mul_integral_weighted"
#check @MethbokeAddon.QuasiFeffermanA.H1Spectral.four_pi_sq_mul_integral_weighted
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.four_pi_sq_mul_integral_weighted"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.four_pi_sq_mul_integral_weighted"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Spectral.four_pi_sq_mul_integral_weighted
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.four_pi_sq_mul_integral_weighted"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_fourier_enstrophy_integrable"
#check @MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_fourier_enstrophy_integrable
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_fourier_enstrophy_integrable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_fourier_enstrophy_integrable"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_fourier_enstrophy_integrable
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_fourier_enstrophy_integrable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_energy_eq_fourier"
#check @MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_energy_eq_fourier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_energy_eq_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_energy_eq_fourier"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_energy_eq_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_energy_eq_fourier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_enstrophy_eq_fourier"
#check @MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_enstrophy_eq_fourier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_enstrophy_eq_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_enstrophy_eq_fourier"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_enstrophy_eq_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_enstrophy_eq_fourier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_norm_sq_eq_fourier"
#check @MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_norm_sq_eq_fourier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_norm_sq_eq_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_norm_sq_eq_fourier"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_norm_sq_eq_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_norm_sq_eq_fourier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_weighted_lintegral_eq"
#check @MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_weighted_lintegral_eq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_weighted_lintegral_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_weighted_lintegral_eq"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_weighted_lintegral_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_weighted_lintegral_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_weighted_lintegral_finite"
#check @MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_weighted_lintegral_finite
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_weighted_lintegral_finite"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_weighted_lintegral_finite"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_weighted_lintegral_finite
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Spectral.physicalH1_weighted_lintegral_finite"
