import QFAEnstrophyCoefficient.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Interval ENNReal
open MethbokeAddon.QuasiFeffermanA

namespace QFAEnstrophyCoefficient.ExpectedTypes

-- Explicit polynomial and inequality types; no alias of the proved statement.
example : ∀ N V : ℝ,
    (3 * N - 2 * V) ^ 2 * (3 * N ^ 2 + 4 * N * V + 4 * V ^ 2) =
      27 * N ^ 4 - 32 * N * V ^ 3 + 16 * V ^ 4 :=
  enstrophy_young_polynomial_identity

example : ∀ {N V : ℝ}, 0 ≤ N → 0 ≤ V →
    32 * N * V ^ 3 ≤ 27 * N ^ 4 + 16 * V ^ 4 :=
  @enstrophy_young_polynomial_bound

example : ∀ {N K Z ν : ℝ}, 0 ≤ N → 0 ≤ K → 0 ≤ Z → 0 < ν →
    N ^ 4 ≤ K * Z ^ 3 → 2 * N ≤ ν * Z + 27 * K / (16 * ν ^ 3) :=
  @enstrophy_fourth_power_young_bound

-- Both substantive scalar estimates remain explicit premises.
example : ∀ {S ν Y Z N d : ℝ},
    0 ≤ S → 0 < ν → 0 ≤ Y → 0 ≤ Z → 0 ≤ N →
    N ^ 4 ≤ S ^ 6 * Y ^ 3 * Z ^ 3 → d + 2 * ν * Z ≤ 2 * N →
    d + ν * Z ≤ (27 * S ^ 6 / (16 * ν ^ 3)) * Y ^ 3 :=
  @enstrophy_cubic_of_fourth_power

example : ∀ {S ν : ℝ}, 0 < ν → S ^ 6 = 16 / (27 * Real.pi ^ 4) →
    27 * S ^ 6 / (16 * ν ^ 3) = 1 / (Real.pi ^ 4 * ν ^ 3) :=
  @enstrophy_coefficient_eq_pi

example : ∀ {S ν Y Z N d : ℝ},
    0 ≤ S → 0 < ν → 0 ≤ Y → 0 ≤ Z → 0 ≤ N →
    S ^ 6 = 16 / (27 * Real.pi ^ 4) →
    N ^ 4 ≤ S ^ 6 * Y ^ 3 * Z ^ 3 → d + 2 * ν * Z ≤ 2 * N →
    d + ν * Z ≤ (1 / (Real.pi ^ 4 * ν ^ 3)) * Y ^ 3 :=
  @enstrophy_cubic_pi_of_fourth_power

example : ∀ {S ν Y Z N d : ℝ},
    0 ≤ S → 0 < ν → 0 ≤ Y → 0 ≤ Z → 0 ≤ N →
    S ^ 6 = 16 / (27 * Real.pi ^ 4) →
    N ^ 4 ≤ S ^ 6 * Y ^ 3 * Z ^ 3 → d + 2 * ν * Z ≤ 2 * N →
    d ≤ (1 / (Real.pi ^ 4 * ν ^ 3)) * Y ^ 3 :=
  @enstrophy_cubic_pi_without_dissipation

-- Literal full terminal integral and AC hypotheses are retained. There is
-- no NSE constructor, hidden continuation premise or value required at b.
example : ∀ {Y Z N : ℝ → ℝ} {S ν b : ℝ},
    0 ≤ S → 0 < ν → 0 ≤ Y 0 →
    S ^ 6 = 16 / (27 * Real.pi ^ 4) →
    (∀ R ∈ Ico (0 : ℝ) b, AbsolutelyContinuousOnInterval Y 0 R) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), 0 ≤ Y t) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), 0 ≤ Z t) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), 0 ≤ N t) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b),
      (N t) ^ 4 ≤ S ^ 6 * (Y t) ^ 3 * (Z t) ^ 3) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b),
      deriv Y t + 2 * ν * Z t ≤ 2 * N t) →
    (∫⁻ r in Ioo (0 : ℝ) b, ENNReal.ofReal ((Y r) ^ 2)) ≠ ∞ →
    ∀ t ∈ Ico (0 : ℝ) b,
      Y t ≤ Y 0 * Real.exp ((1 / (Real.pi ^ 4 * ν ^ 3)) *
        (∫⁻ r in Ioo (0 : ℝ) b, ENNReal.ofReal ((Y r) ^ 2)).toReal) :=
  @enstrophy_uniform_of_fourth_power_finite_budget

end QFAEnstrophyCoefficient.ExpectedTypes

end

-- Named reports below execute only in the authorized external verification.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_young_polynomial_identity"
#check @MethbokeAddon.QuasiFeffermanA.enstrophy_young_polynomial_identity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.enstrophy_young_polynomial_identity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_young_polynomial_identity"
#print axioms MethbokeAddon.QuasiFeffermanA.enstrophy_young_polynomial_identity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.enstrophy_young_polynomial_identity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_young_polynomial_bound"
#check @MethbokeAddon.QuasiFeffermanA.enstrophy_young_polynomial_bound
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.enstrophy_young_polynomial_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_young_polynomial_bound"
#print axioms MethbokeAddon.QuasiFeffermanA.enstrophy_young_polynomial_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.enstrophy_young_polynomial_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_fourth_power_young_bound"
#check @MethbokeAddon.QuasiFeffermanA.enstrophy_fourth_power_young_bound
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.enstrophy_fourth_power_young_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_fourth_power_young_bound"
#print axioms MethbokeAddon.QuasiFeffermanA.enstrophy_fourth_power_young_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.enstrophy_fourth_power_young_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_of_fourth_power"
#check @MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_of_fourth_power
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_of_fourth_power"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_of_fourth_power"
#print axioms MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_of_fourth_power
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_of_fourth_power"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_coefficient_eq_pi"
#check @MethbokeAddon.QuasiFeffermanA.enstrophy_coefficient_eq_pi
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.enstrophy_coefficient_eq_pi"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_coefficient_eq_pi"
#print axioms MethbokeAddon.QuasiFeffermanA.enstrophy_coefficient_eq_pi
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.enstrophy_coefficient_eq_pi"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_pi_of_fourth_power"
#check @MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_pi_of_fourth_power
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_pi_of_fourth_power"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_pi_of_fourth_power"
#print axioms MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_pi_of_fourth_power
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_pi_of_fourth_power"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_pi_without_dissipation"
#check @MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_pi_without_dissipation
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_pi_without_dissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_pi_without_dissipation"
#print axioms MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_pi_without_dissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.enstrophy_cubic_pi_without_dissipation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_uniform_of_fourth_power_finite_budget"
#check @MethbokeAddon.QuasiFeffermanA.enstrophy_uniform_of_fourth_power_finite_budget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.enstrophy_uniform_of_fourth_power_finite_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.enstrophy_uniform_of_fourth_power_finite_budget"
#print axioms MethbokeAddon.QuasiFeffermanA.enstrophy_uniform_of_fourth_power_finite_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.enstrophy_uniform_of_fourth_power_finite_budget"
