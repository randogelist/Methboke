import MethbokeAddon.QuasiFeffermanA.ACBudget
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Exact scalar extraction of the cubic enstrophy coefficient

The input is an explicit fourth-power convection bound and an explicit scalar
enstrophy inequality. An exact polynomial certificate gives the coefficient
`27 * S^6 / (16 * ν^3)`, which becomes `1 / (π^4 * ν^3)` under the stated
sixth-power equality. No Sobolev admissibility or physical NSE solution is
assumed to have been constructed by this file.

The final composition retains the actual AC, a.e. scalar evolution, and finite
full stopped-budget premises. It concludes a uniform scalar bound only.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Interval ENNReal

namespace MethbokeAddon.QuasiFeffermanA

/-- Exact polynomial certificate for the fourth-power Young estimate. -/
theorem enstrophy_young_polynomial_identity (N V : ℝ) :
    (3 * N - 2 * V) ^ 2 * (3 * N ^ 2 + 4 * N * V + 4 * V ^ 2) =
      27 * N ^ 4 - 32 * N * V ^ 3 + 16 * V ^ 4 := by
  ring

/-- The polynomial certificate is nonnegative for nonnegative inputs. -/
theorem enstrophy_young_polynomial_bound {N V : ℝ}
    (hN : 0 ≤ N) (hV : 0 ≤ V) :
    32 * N * V ^ 3 ≤ 27 * N ^ 4 + 16 * V ^ 4 := by
  have hquad : 0 ≤ 3 * N ^ 2 + 4 * N * V + 4 * V ^ 2 := by positivity
  have hprod := mul_nonneg (sq_nonneg (3 * N - 2 * V)) hquad
  rw [enstrophy_young_polynomial_identity] at hprod
  linarith

/-- Extract a usable Young estimate directly from a fourth-power bound.
The `Z = 0` case is proved separately before any cancellation. -/
theorem enstrophy_fourth_power_young_bound {N K Z ν : ℝ}
    (hN : 0 ≤ N) (hK : 0 ≤ K) (hZ : 0 ≤ Z) (hν : 0 < ν)
    (hfourth : N ^ 4 ≤ K * Z ^ 3) :
    2 * N ≤ ν * Z + 27 * K / (16 * ν ^ 3) := by
  by_cases hZzero : Z = 0
  · have hNfourth : N ^ 4 = 0 :=
      le_antisymm (by simpa [hZzero] using hfourth) (by positivity)
    have hNzero : N = 0 := (pow_eq_zero_iff (by norm_num : 4 ≠ 0)).mp hNfourth
    have hquot : 0 ≤ 27 * K / (16 * ν ^ 3) := by positivity
    simpa only [hNzero, hZzero, mul_zero, zero_add] using hquot
  · have hZpos : 0 < Z := lt_of_le_of_ne hZ (Ne.symm hZzero)
    have hpoly := enstrophy_young_polynomial_bound hN (mul_nonneg hν.le hZ)
    have hscaled : 32 * N * ν ^ 3 ≤ 27 * K + 16 * ν ^ 4 * Z := by
      apply (mul_le_mul_iff_left₀ (pow_pos hZpos 3)).mp
      calc
        (32 * N * ν ^ 3) * Z ^ 3 = 32 * N * (ν * Z) ^ 3 := by ring
        _ ≤ 27 * N ^ 4 + 16 * (ν * Z) ^ 4 := hpoly
        _ ≤ 27 * (K * Z ^ 3) + 16 * (ν * Z) ^ 4 := by
          have hmul : 27 * N ^ 4 ≤ 27 * (K * Z ^ 3) :=
            mul_le_mul_of_nonneg_left hfourth (by norm_num : (0 : ℝ) ≤ 27)
          linarith only [hmul]
        _ = (27 * K + 16 * ν ^ 4 * Z) * Z ^ 3 := by ring
    have hdivide : 2 * N - ν * Z ≤ 27 * K / (16 * ν ^ 3) := by
      apply (le_div_iff₀ (by positivity : 0 < 16 * ν ^ 3)).mpr
      nlinarith only [hscaled]
    linarith

/-- The explicit fourth-power convection estimate and scalar enstrophy
inequality imply the exact cubic coefficient, with one dissipation term kept. -/
theorem enstrophy_cubic_of_fourth_power {S ν Y Z N d : ℝ}
    (hS : 0 ≤ S) (hν : 0 < ν) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hN : 0 ≤ N)
    (hfourth : N ^ 4 ≤ S ^ 6 * Y ^ 3 * Z ^ 3)
    (henstrophy : d + 2 * ν * Z ≤ 2 * N) :
    d + ν * Z ≤ (27 * S ^ 6 / (16 * ν ^ 3)) * Y ^ 3 := by
  have hYoung := enstrophy_fourth_power_young_bound hN
    (by positivity : 0 ≤ S ^ 6 * Y ^ 3) hZ hν hfourth
  calc
    d + ν * Z ≤ 27 * (S ^ 6 * Y ^ 3) / (16 * ν ^ 3) := by linarith
    _ = (27 * S ^ 6 / (16 * ν ^ 3)) * Y ^ 3 := by ring

/-- Pure arithmetic specialization. The sixth-power equality is a premise,
not a theorem of sharp spatial Sobolev admissibility. -/
theorem enstrophy_coefficient_eq_pi {S ν : ℝ}
    (hν : 0 < ν) (hS6 : S ^ 6 = 16 / (27 * Real.pi ^ 4)) :
    27 * S ^ 6 / (16 * ν ^ 3) = 1 / (Real.pi ^ 4 * ν ^ 3) := by
  rw [hS6]
  field_simp [ne_of_gt hν, Real.pi_ne_zero] <;> ring

/-- Registered coefficient under the explicit sharp-normalization equality,
still conditional on the supplied scalar spatial and evolution estimates. -/
theorem enstrophy_cubic_pi_of_fourth_power {S ν Y Z N d : ℝ}
    (hS : 0 ≤ S) (hν : 0 < ν) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hN : 0 ≤ N)
    (hS6 : S ^ 6 = 16 / (27 * Real.pi ^ 4))
    (hfourth : N ^ 4 ≤ S ^ 6 * Y ^ 3 * Z ^ 3)
    (henstrophy : d + 2 * ν * Z ≤ 2 * N) :
    d + ν * Z ≤ (1 / (Real.pi ^ 4 * ν ^ 3)) * Y ^ 3 := by
  have hbound := enstrophy_cubic_of_fourth_power hS hν hY hZ hN hfourth henstrophy
  rw [enstrophy_coefficient_eq_pi hν hS6] at hbound
  exact hbound

/-- Dropping the retained nonnegative dissipation yields the cubic scalar
derivative estimate consumed by the AC budget theorem. -/
theorem enstrophy_cubic_pi_without_dissipation {S ν Y Z N d : ℝ}
    (hS : 0 ≤ S) (hν : 0 < ν) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hN : 0 ≤ N)
    (hS6 : S ^ 6 = 16 / (27 * Real.pi ^ 4))
    (hfourth : N ^ 4 ≤ S ^ 6 * Y ^ 3 * Z ^ 3)
    (henstrophy : d + 2 * ν * Z ≤ 2 * N) :
    d ≤ (1 / (Real.pi ^ 4 * ν ^ 3)) * Y ^ 3 := by
  have hbound := enstrophy_cubic_pi_of_fourth_power hS hν hY hZ hN hS6
    hfourth henstrophy
  have hdiss : 0 ≤ ν * Z := mul_nonneg hν.le hZ
  linarith

/-- Full scalar chain: a.e. fourth-power/enstrophy estimates, actual AC and
one finite full stopped square budget give a uniform preterminal bound.
The physical NSE realization of every input remains a separate obligation. -/
theorem enstrophy_uniform_of_fourth_power_finite_budget
    {Y Z N : ℝ → ℝ} {S ν b : ℝ}
    (hS : 0 ≤ S) (hν : 0 < ν) (hY0 : 0 ≤ Y 0)
    (hS6 : S ^ 6 = 16 / (27 * Real.pi ^ 4))
    (hY : ∀ R ∈ Ico (0 : ℝ) b, AbsolutelyContinuousOnInterval Y 0 R)
    (hYnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), 0 ≤ Y t)
    (hZnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), 0 ≤ Z t)
    (hNnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), 0 ≤ N t)
    (hfourth : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b),
      (N t) ^ 4 ≤ S ^ 6 * (Y t) ^ 3 * (Z t) ^ 3)
    (henstrophy : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b),
      deriv Y t + 2 * ν * Z t ≤ 2 * N t)
    (hbudget : stoppedSquareBudget Y b ≠ ∞) :
    ∀ t ∈ Ico (0 : ℝ) b,
      Y t ≤ Y 0 * Real.exp
        ((1 / (Real.pi ^ 4 * ν ^ 3)) * (stoppedSquareBudget Y b).toReal) := by
  have hcubic : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b),
      deriv Y t ≤ (1 / (Real.pi ^ 4 * ν ^ 3)) * (Y t) ^ 3 := by
    filter_upwards [hYnn, hZnn, hNnn, hfourth, henstrophy] with t hYt hZt hNt hFt hEt
    exact enstrophy_cubic_pi_without_dissipation hS hν hYt hZt hNt hS6 hFt hEt
  exact ac_cubic_uniform_of_finite_stopped_budget (by positivity) hY0 hY hcubic hbudget

end MethbokeAddon.QuasiFeffermanA
