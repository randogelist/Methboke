import EhrenfestPhysicalForcing.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-! Independently stated consumer types; fresh external evidence required. -/

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff RealInnerProductSpace
open MethbokeAddon.EhrenfestObstruction

example (N : ℕ) (c : FourierCoeff) (hreal : SpectralReality c) :
    MeanZero (finiteSynthesis N c) :=
  finiteSynthesis_meanZero_of_reality N c hreal

example :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ N : ℕ,
      ∀ c : FourierCoeff,
      (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0) →
      SpectralReality c → SpectralSolenoidal c →
      -2 * coefficientEnstrophyNonlinearPower N c ≤
        ν * coefficientLaplacianSquare N c +
          C / ν ^ 3 * (coefficientDissipation N c) ^ 3 :=
  FINITE_ERROR_ABSORPTION_FROM_PHYSICAL

example (N : ℕ) (c f : FourierCoeff) :
    dissipationRatePairing N c (cutoffCoeff N f) =
      dissipationRatePairing N c f :=
  dissipationRatePairing_cutoff_right N c f

example (N : ℕ) (c f : FourierCoeff) (hsol : SpectralSolenoidal c) :
    dissipationRatePairing N c (fun k => coefficientLeray k (f k)) =
      dissipationRatePairing N c f :=
  dissipationRatePairing_leray_right N c f hsol

example (N : ℕ) (c : FourierCoeff) (F : Field) (hF : Continuous F) :
    dissipationRatePairing N c (datumFourierCoeff F) =
      -2 * (∫ x in unitCube,
        inner ℝ (laplacian (finiteSynthesis N c) x) (F x)) :=
  dissipationRatePairing_fourier_eq_physical N c F hF

example (δ : ℝ) (hδ : 0 < δ) (a b : Vec) :
    -2 * inner ℝ a b ≤ δ * ‖a‖ ^ 2 + ‖b‖ ^ 2 / δ :=
  physical_inner_young δ hδ a b

example (δ : ℝ) (hδ : 0 < δ) (a b : Field)
    (ha : Continuous a) (hb : Continuous b) :
    -2 * (∫ x in unitCube, inner ℝ (a x) (b x)) ≤
      δ * (∫ x in unitCube, ‖a x‖ ^ 2) +
        (∫ x in unitCube, ‖b x‖ ^ 2) / δ :=
  physical_integral_inner_young δ hδ a b ha hb

example (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c)
    (F : Field) (hF : Continuous F) :
    dissipationRatePairing N c
        (cutoffCoeff N (fun k => coefficientLeray k (datumFourierCoeff F k))) ≤
      δ * coefficientLaplacianSquare N c +
        (∫ x in unitCube, ‖F x‖ ^ 2) / δ :=
  dissipationRatePairing_projected_forcing_le δ hδ N c hreal hsol F hF

example :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ N : ℕ,
      ∀ c : ℝ → FourierCoeff, ∀ F : Field, Continuous F →
      ∀ s : Set ℝ, ∀ t : ℝ,
      (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c t k i = 0) →
      SpectralReality (c t) → SpectralSolenoidal (c t) →
      (∀ k ∈ cutoffModes N, ∀ i : Fin 3,
        HasDerivWithinAt (fun r => c r k i)
          (galerkinRhs ν N (c t) k i +
            cutoffCoeff N
              (fun l => coefficientLeray l (datumFourierCoeff F l)) k i) s t) →
      ∃ d : ℝ,
        HasDerivWithinAt (fun r => coefficientDissipation N (c r)) d s t ∧
        d + (ν / 2) * coefficientLaplacianSquare N (c t) ≤
          C / ν ^ 3 * (coefficientDissipation N (c t)) ^ 3 +
            (2 / ν) * (∫ x in unitCube, ‖F x‖ ^ 2) :=
  PHYSICAL_FORCED_ERROR_ENSTROPHY_INEQUALITY


#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_meanZero_of_reality"
#check @MethbokeAddon.EhrenfestObstruction.finiteSynthesis_meanZero_of_reality
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_meanZero_of_reality"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_meanZero_of_reality"
#print axioms MethbokeAddon.EhrenfestObstruction.finiteSynthesis_meanZero_of_reality
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.finiteSynthesis_meanZero_of_reality"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_ABSORPTION_FROM_PHYSICAL"
#check @MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_ABSORPTION_FROM_PHYSICAL
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_ABSORPTION_FROM_PHYSICAL"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_ABSORPTION_FROM_PHYSICAL"
#print axioms MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_ABSORPTION_FROM_PHYSICAL
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_ABSORPTION_FROM_PHYSICAL"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_cutoff_right"
#check @MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_cutoff_right
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_cutoff_right"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_cutoff_right"
#print axioms MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_cutoff_right
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_cutoff_right"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_leray_right"
#check @MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_leray_right
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_leray_right"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_leray_right"
#print axioms MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_leray_right
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_leray_right"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_fourier_eq_physical"
#check @MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_fourier_eq_physical
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_fourier_eq_physical"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_fourier_eq_physical"
#print axioms MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_fourier_eq_physical
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_fourier_eq_physical"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physical_inner_young"
#check @MethbokeAddon.EhrenfestObstruction.physical_inner_young
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physical_inner_young"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physical_inner_young"
#print axioms MethbokeAddon.EhrenfestObstruction.physical_inner_young
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physical_inner_young"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physical_integral_inner_young"
#check @MethbokeAddon.EhrenfestObstruction.physical_integral_inner_young
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physical_integral_inner_young"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physical_integral_inner_young"
#print axioms MethbokeAddon.EhrenfestObstruction.physical_integral_inner_young
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physical_integral_inner_young"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_projected_forcing_le"
#check @MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_projected_forcing_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_projected_forcing_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_projected_forcing_le"
#print axioms MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_projected_forcing_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_projected_forcing_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.PHYSICAL_FORCED_ERROR_ENSTROPHY_INEQUALITY"
#check @MethbokeAddon.EhrenfestObstruction.PHYSICAL_FORCED_ERROR_ENSTROPHY_INEQUALITY
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.PHYSICAL_FORCED_ERROR_ENSTROPHY_INEQUALITY"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.PHYSICAL_FORCED_ERROR_ENSTROPHY_INEQUALITY"
#print axioms MethbokeAddon.EhrenfestObstruction.PHYSICAL_FORCED_ERROR_ENSTROPHY_INEQUALITY
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.PHYSICAL_FORCED_ERROR_ENSTROPHY_INEQUALITY"

