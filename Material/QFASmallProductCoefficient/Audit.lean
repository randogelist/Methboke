import QFASmallProductCoefficient.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MethbokeAddon.QuasiFeffermanA

namespace QFASmallProductCoefficient.ExpectedTypes

-- Independent full consumer types expand the registered threshold literally.
example : ∀ {S ν W q : ℝ}, 0 < S → 0 < ν → 0 ≤ q →
    q ^ 4 ≤ S ^ 6 * W → W < ν ^ 4 / S ^ 6 → q < ν :=
  @smallProduct_coefficient_lt_viscosity

example : ∀ {S W q : ℝ}, q ^ 4 ≤ S ^ 6 * W → W = 0 → q = 0 :=
  @smallProduct_coefficient_eq_zero_of_product_zero

example : ∀ {d ν q Z : ℝ}, d + 2 * ν * Z ≤ 2 * q * Z →
    d + 2 * (ν - q) * Z ≤ 0 :=
  @smallProduct_retained_dissipation

example : ∀ {S ν W q d Z : ℝ}, 0 < S → 0 < ν → 0 ≤ q →
    q ^ 4 ≤ S ^ 6 * W → W < ν ^ 4 / S ^ 6 →
    d + 2 * ν * Z ≤ 2 * q * Z →
    0 < ν - q ∧ d + 2 * (ν - q) * Z ≤ 0 :=
  @smallProduct_positive_gap_and_dissipation

example : ∀ {S ν W q d Z : ℝ}, 0 < S → 0 < ν → 0 ≤ q → 0 ≤ Z →
    q ^ 4 ≤ S ^ 6 * W → W < ν ^ 4 / S ^ 6 →
    d + 2 * ν * Z ≤ 2 * q * Z → d ≤ 0 :=
  @smallProduct_derivative_nonpos

example : ∀ {S ν W q d Z : ℝ}, 0 < S → 0 < ν → 0 ≤ q → 0 < Z →
    q ^ 4 ≤ S ^ 6 * W → W < ν ^ 4 / S ^ 6 →
    d + 2 * ν * Z ≤ 2 * q * Z → d < 0 :=
  @smallProduct_derivative_neg

end QFASmallProductCoefficient.ExpectedTypes

end

-- These named reports execute only in authorized external verification.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.smallProduct_coefficient_lt_viscosity"
#check @MethbokeAddon.QuasiFeffermanA.smallProduct_coefficient_lt_viscosity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.smallProduct_coefficient_lt_viscosity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.smallProduct_coefficient_lt_viscosity"
#print axioms MethbokeAddon.QuasiFeffermanA.smallProduct_coefficient_lt_viscosity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.smallProduct_coefficient_lt_viscosity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.smallProduct_coefficient_eq_zero_of_product_zero"
#check @MethbokeAddon.QuasiFeffermanA.smallProduct_coefficient_eq_zero_of_product_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.smallProduct_coefficient_eq_zero_of_product_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.smallProduct_coefficient_eq_zero_of_product_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.smallProduct_coefficient_eq_zero_of_product_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.smallProduct_coefficient_eq_zero_of_product_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.smallProduct_retained_dissipation"
#check @MethbokeAddon.QuasiFeffermanA.smallProduct_retained_dissipation
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.smallProduct_retained_dissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.smallProduct_retained_dissipation"
#print axioms MethbokeAddon.QuasiFeffermanA.smallProduct_retained_dissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.smallProduct_retained_dissipation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.smallProduct_positive_gap_and_dissipation"
#check @MethbokeAddon.QuasiFeffermanA.smallProduct_positive_gap_and_dissipation
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.smallProduct_positive_gap_and_dissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.smallProduct_positive_gap_and_dissipation"
#print axioms MethbokeAddon.QuasiFeffermanA.smallProduct_positive_gap_and_dissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.smallProduct_positive_gap_and_dissipation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.smallProduct_derivative_nonpos"
#check @MethbokeAddon.QuasiFeffermanA.smallProduct_derivative_nonpos
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.smallProduct_derivative_nonpos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.smallProduct_derivative_nonpos"
#print axioms MethbokeAddon.QuasiFeffermanA.smallProduct_derivative_nonpos
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.smallProduct_derivative_nonpos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.smallProduct_derivative_neg"
#check @MethbokeAddon.QuasiFeffermanA.smallProduct_derivative_neg
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.smallProduct_derivative_neg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.smallProduct_derivative_neg"
#print axioms MethbokeAddon.QuasiFeffermanA.smallProduct_derivative_neg
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.smallProduct_derivative_neg"
