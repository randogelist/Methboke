import EhrenfestEventualEnstrophyBound.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-! Independent exact consumer types; external evidence pending. -/


section Consumer1
open Set Filter SingularClosure
open MethbokeAddon.WeakFouriermanB
open scoped Topology

namespace MethbokeAddon.EhrenfestObstruction

-- Independently stated expected types for authorized external cached CI.

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (S T : ℝ) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a.val u p) (hTS : T < S)
    (n : ℕ) (k : Frequency) (i : Fin 3) :
    ContinuousOn (fun t => canonicalErrorCoeff ν hν a u n t k i)
      (Icc (0 : ℝ) T) :=
  canonicalErrorCoeff_continuousOn_Icc ν hν a S T u p H hTS n k i

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (S T : ℝ) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a.val u p) (hTS : T < S) (n : ℕ) :
    ContinuousOn
      (fun t => coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n t))
      (Icc (0 : ℝ) T) :=
  canonical_error_dissipation_continuousOn_Icc ν hν a S T u p H hTS n

example (A : ℝ) :
    Tendsto (fun n : ℕ => A / (((n + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) :=
  forcing_div_nat_succ_sq_tendsto_zero A

-- The final consumer expands the actual canonical choice and normalization;
-- no uniform error, reference, or Galerkin bound is an input premise.
example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (S T : ℝ) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a.val u p) (hTS : T < S) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T,
      coefficientDissipation (n + 1)
        ((canonicalGalerkinSolution ν hν a.val a.property (n + 1)).coeff t) / 2 ≤ C :=
  initial_front_eventual_canonical_enstrophy_bound ν hν a S T u p H hTS


end MethbokeAddon.EhrenfestObstruction
end Consumer1


#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_continuousOn_Icc"
#check @MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_continuousOn_Icc"
#print axioms MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_error_dissipation_continuousOn_Icc"
#check @MethbokeAddon.EhrenfestObstruction.canonical_error_dissipation_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_error_dissipation_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_error_dissipation_continuousOn_Icc"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_error_dissipation_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_error_dissipation_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.forcing_div_nat_succ_sq_tendsto_zero"
#check @MethbokeAddon.EhrenfestObstruction.forcing_div_nat_succ_sq_tendsto_zero
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.forcing_div_nat_succ_sq_tendsto_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.forcing_div_nat_succ_sq_tendsto_zero"
#print axioms MethbokeAddon.EhrenfestObstruction.forcing_div_nat_succ_sq_tendsto_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.forcing_div_nat_succ_sq_tendsto_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_eventual_canonical_enstrophy_bound"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_eventual_canonical_enstrophy_bound
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_eventual_canonical_enstrophy_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_eventual_canonical_enstrophy_bound"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_eventual_canonical_enstrophy_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_eventual_canonical_enstrophy_bound"
