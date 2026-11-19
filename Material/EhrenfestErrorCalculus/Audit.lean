import EhrenfestErrorCalculus.Endpoint

set_option autoImplicit false
open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff RealInnerProductSpace
open MethbokeAddon.EhrenfestObstruction

example (N : ℕ) (c : ℝ → FourierCoeff) (d : FourierCoeff)
    {s : Set ℝ} {t : ℝ}
    (hc : ∀ k ∈ cutoffModes N, ∀ i : Fin 3,
      HasDerivWithinAt (fun r => c r k i) (d k i) s t) :
    HasDerivWithinAt (fun r => coefficientDissipation N (c r))
      (dissipationRatePairing N (c t) d) s t :=
  coefficient_dissipation_hasDerivWithinAt N c d hc

example (N : ℕ) (c v : ℝ → FourierCoeff) (dc dv : FourierCoeff)
    {s : Set ℝ} {t : ℝ}
    (hc : ∀ k ∈ cutoffModes N, ∀ i : Fin 3,
      HasDerivWithinAt (fun r => c r k i) (dc k i) s t)
    (hv : ∀ k ∈ cutoffModes N, ∀ i : Fin 3,
      HasDerivWithinAt (fun r => v r k i) (dv k i) s t) :
    HasDerivWithinAt (fun r => coefficientDissipation N (c r - v r))
      (dissipationRatePairing N (c t - v t) (dc - dv)) s t :=
  coefficient_error_dissipation_hasDerivWithinAt N c v dc dv hc hv

example (N : ℕ) (c d f : FourierCoeff) :
    dissipationRatePairing N c (d + f) =
      dissipationRatePairing N c d + dissipationRatePairing N c f :=
  dissipationRatePairing_add_right N c d f

example (N : ℕ) (c d f : FourierCoeff) :
    dissipationRatePairing N c (d - f) =
      dissipationRatePairing N c d - dissipationRatePairing N c f :=
  dissipationRatePairing_sub_right N c d f

example (ν : ℝ) (N : ℕ) (c : FourierCoeff) :
    dissipationRatePairing N c (galerkinRhs ν N c) =
      (-2 * ν) * coefficientLaplacianSquare N c -
        2 * coefficientEnstrophyNonlinearPower N c :=
  dissipationRatePairing_galerkinRhs ν N c

example (ν : ℝ) (N : ℕ) (c : ℝ → FourierCoeff) (f : FourierCoeff)
    {s : Set ℝ} {t : ℝ}
    (heq : ∀ k ∈ cutoffModes N, ∀ i : Fin 3,
      HasDerivWithinAt (fun r => c r k i)
        (galerkinRhs ν N (c t) k i + f k i) s t) :
    HasDerivWithinAt (fun r => coefficientDissipation N (c r))
      ((-2 * ν) * coefficientLaplacianSquare N (c t) -
        2 * coefficientEnstrophyNonlinearPower N (c t) +
        dissipationRatePairing N (c t) f) s t :=
  forced_coefficient_dissipation_identity ν N c f heq

example :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ N : ℕ,
      ∀ c : FourierCoeff,
      (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0) →
      SpectralReality c → SpectralSolenoidal c →
      -2 * coefficientEnstrophyNonlinearPower N c ≤
        ν * coefficientLaplacianSquare N c +
          C / ν ^ 3 * (coefficientDissipation N c) ^ 3 :=
  FINITE_ERROR_NONLINEAR_ABSORPTION

example :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ N : ℕ,
      ∀ c : ℝ → FourierCoeff, ∀ f : FourierCoeff,
      ∀ s : Set ℝ, ∀ t : ℝ,
      (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c t k i = 0) →
      SpectralReality (c t) → SpectralSolenoidal (c t) →
      (∀ k ∈ cutoffModes N, ∀ i : Fin 3,
        HasDerivWithinAt (fun r => c r k i)
          (galerkinRhs ν N (c t) k i + f k i) s t) →
      ∃ d : ℝ,
        HasDerivWithinAt (fun r => coefficientDissipation N (c r)) d s t ∧
        d + ν * coefficientLaplacianSquare N (c t) ≤
          C / ν ^ 3 * (coefficientDissipation N (c t)) ^ 3 +
            dissipationRatePairing N (c t) f :=
  FORCED_COEFFICIENT_ENSTROPHY_INEQUALITY

set_option pp.universes true

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficient_dissipation_hasDerivWithinAt"
#check @MethbokeAddon.EhrenfestObstruction.coefficient_dissipation_hasDerivWithinAt
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.coefficient_dissipation_hasDerivWithinAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficient_dissipation_hasDerivWithinAt"
#print axioms MethbokeAddon.EhrenfestObstruction.coefficient_dissipation_hasDerivWithinAt
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.coefficient_dissipation_hasDerivWithinAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficient_error_dissipation_hasDerivWithinAt"
#check @MethbokeAddon.EhrenfestObstruction.coefficient_error_dissipation_hasDerivWithinAt
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.coefficient_error_dissipation_hasDerivWithinAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficient_error_dissipation_hasDerivWithinAt"
#print axioms MethbokeAddon.EhrenfestObstruction.coefficient_error_dissipation_hasDerivWithinAt
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.coefficient_error_dissipation_hasDerivWithinAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_add_right"
#check @MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_add_right
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_add_right"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_add_right"
#print axioms MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_add_right
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_add_right"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_sub_right"
#check @MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_sub_right
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_sub_right"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_sub_right"
#print axioms MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_sub_right
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_sub_right"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_galerkinRhs"
#check @MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_galerkinRhs
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_galerkinRhs"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_galerkinRhs"
#print axioms MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_galerkinRhs
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.dissipationRatePairing_galerkinRhs"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.forced_coefficient_dissipation_identity"
#check @MethbokeAddon.EhrenfestObstruction.forced_coefficient_dissipation_identity
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.forced_coefficient_dissipation_identity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.forced_coefficient_dissipation_identity"
#print axioms MethbokeAddon.EhrenfestObstruction.forced_coefficient_dissipation_identity
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.forced_coefficient_dissipation_identity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_NONLINEAR_ABSORPTION"
#check @MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_NONLINEAR_ABSORPTION
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_NONLINEAR_ABSORPTION"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_NONLINEAR_ABSORPTION"
#print axioms MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_NONLINEAR_ABSORPTION
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_NONLINEAR_ABSORPTION"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.FORCED_COEFFICIENT_ENSTROPHY_INEQUALITY"
#check @MethbokeAddon.EhrenfestObstruction.FORCED_COEFFICIENT_ENSTROPHY_INEQUALITY
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.FORCED_COEFFICIENT_ENSTROPHY_INEQUALITY"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.FORCED_COEFFICIENT_ENSTROPHY_INEQUALITY"
#print axioms MethbokeAddon.EhrenfestObstruction.FORCED_COEFFICIENT_ENSTROPHY_INEQUALITY
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.FORCED_COEFFICIENT_ENSTROPHY_INEQUALITY"

