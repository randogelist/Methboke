import MethbokeAddon.QuasiFeffermanA.Cutoff
import Mathlib.Tactic

/-!
# Exact strict small-product coefficient and retained dissipation

The coefficient bound and scalar balance are explicit premises. They are not
asserted to arise from a physical PDE or a sharp Sobolev inequality here.
The strict registered product threshold forces a positive viscosity margin;
the algebra preserves that margin in the retained dissipation inequality.

Actual spatial admission, time absolute continuity, first-crossing invariance
and strong-solution continuation remain separate obligations.
-/

set_option autoImplicit false

noncomputable section

namespace MethbokeAddon.QuasiFeffermanA

/-- The exact registered product threshold makes the supplied nonnegative
coefficient strictly smaller than viscosity. -/
theorem smallProduct_coefficient_lt_viscosity {S ν W q : ℝ}
    (hS : 0 < S) (hν : 0 < ν) (hq : 0 ≤ q)
    (hfourth : q ^ 4 ≤ S ^ 6 * W)
    (hsub : W < productThreshold S ν) :
    q < ν := by
  change W < ν ^ 4 / S ^ 6 at hsub
  have hscaled : W * S ^ 6 < ν ^ 4 :=
    (lt_div_iff₀ (pow_pos hS 6)).mp hsub
  have hstrict : S ^ 6 * W < ν ^ 4 := by
    simpa only [mul_comm] using hscaled
  have hqfourth : q ^ 4 < ν ^ 4 := hfourth.trans_lt hstrict
  by_contra hnot
  have hνq : ν ≤ q := le_of_not_gt hnot
  have hpow : ν ^ 4 ≤ q ^ 4 := pow_le_pow_left₀ hν.le hνq 4
  exact (not_lt_of_ge hpow) hqfourth

/-- Zero product forces the supplied coefficient to vanish, without division
by the product, dissipation or coefficient. -/
theorem smallProduct_coefficient_eq_zero_of_product_zero {S W q : ℝ}
    (hfourth : q ^ 4 ≤ S ^ 6 * W) (hzero : W = 0) :
    q = 0 := by
  have hqfourth : q ^ 4 = 0 :=
    le_antisymm (by simpa [hzero] using hfourth) (by positivity)
  exact (pow_eq_zero_iff (by norm_num : 4 ≠ 0)).mp hqfourth

/-- Exact rearrangement retaining the full viscosity margin. -/
theorem smallProduct_retained_dissipation {d ν q Z : ℝ}
    (hbalance : d + 2 * ν * Z ≤ 2 * q * Z) :
    d + 2 * (ν - q) * Z ≤ 0 := by
  nlinarith only [hbalance]

/-- Strict product smallness and the supplied balance yield a positive
viscosity margin together with the retained dissipation estimate. -/
theorem smallProduct_positive_gap_and_dissipation {S ν W q d Z : ℝ}
    (hS : 0 < S) (hν : 0 < ν) (hq : 0 ≤ q)
    (hfourth : q ^ 4 ≤ S ^ 6 * W)
    (hsub : W < productThreshold S ν)
    (hbalance : d + 2 * ν * Z ≤ 2 * q * Z) :
    0 < ν - q ∧ d + 2 * (ν - q) * Z ≤ 0 := by
  exact ⟨sub_pos.mpr (smallProduct_coefficient_lt_viscosity hS hν hq hfourth hsub),
    smallProduct_retained_dissipation hbalance⟩

/-- Nonnegative supplied dissipation makes the scalar derivative nonpositive.
This is a pointwise algebra statement, not a temporal invariance theorem. -/
theorem smallProduct_derivative_nonpos {S ν W q d Z : ℝ}
    (hS : 0 < S) (hν : 0 < ν) (hq : 0 ≤ q) (hZ : 0 ≤ Z)
    (hfourth : q ^ 4 ≤ S ^ 6 * W)
    (hsub : W < productThreshold S ν)
    (hbalance : d + 2 * ν * Z ≤ 2 * q * Z) :
    d ≤ 0 := by
  have hcoercive := smallProduct_positive_gap_and_dissipation
    hS hν hq hfourth hsub hbalance
  have hdiss : 0 ≤ 2 * (ν - q) * Z :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hcoercive.1.le) hZ
  linarith only [hcoercive.2, hdiss]

/-- Positive supplied dissipation makes the scalar derivative strictly
negative while the product remains strictly below its threshold. -/
theorem smallProduct_derivative_neg {S ν W q d Z : ℝ}
    (hS : 0 < S) (hν : 0 < ν) (hq : 0 ≤ q) (hZ : 0 < Z)
    (hfourth : q ^ 4 ≤ S ^ 6 * W)
    (hsub : W < productThreshold S ν)
    (hbalance : d + 2 * ν * Z ≤ 2 * q * Z) :
    d < 0 := by
  have hcoercive := smallProduct_positive_gap_and_dissipation
    hS hν hq hfourth hsub hbalance
  have hdiss : 0 < 2 * (ν - q) * Z :=
    mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hcoercive.1) hZ
  linarith only [hcoercive.2, hdiss]

end MethbokeAddon.QuasiFeffermanA
