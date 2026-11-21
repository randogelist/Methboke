import QFAACBudget.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Interval ENNReal
open MethbokeAddon.QuasiFeffermanA

namespace QFAACBudget.ExpectedTypes

-- The initial data are scalar AC and a.e. derivative hypotheses. No Volterra
-- input, NSE constructor, continuation port or endpoint value is inserted.
example : ∀ {Y : ℝ → ℝ} {κ R : ℝ}, 0 ≤ R →
    AbsolutelyContinuousOnInterval Y 0 R →
    (∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), deriv Y r ≤ κ * (Y r) ^ 3) →
    ∀ t ∈ Icc (0 : ℝ) R,
      Y t ≤ Y 0 + ∫ r in (0 : ℝ)..t, κ * (Y r) ^ 3 :=
  @ac_cubic_volterra

example : ∀ {Y : ℝ → ℝ} {κ R : ℝ}, 0 ≤ R → 0 ≤ κ →
    AbsolutelyContinuousOnInterval Y 0 R →
    (∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), deriv Y r ≤ κ * (Y r) ^ 3) →
    ∀ t ∈ Icc (0 : ℝ) R,
      Y t ≤ Y 0 * Real.exp (κ * ∫ r in (0 : ℝ)..t, (Y r) ^ 2) :=
  @ac_cubic_square_budget_bound

example : ∀ {Y : ℝ → ℝ} {κ R M : ℝ}, 0 ≤ R → 0 ≤ κ →
    AbsolutelyContinuousOnInterval Y 0 R → 0 ≤ Y 0 →
    (∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), deriv Y r ≤ κ * (Y r) ^ 3) →
    (∫ r in (0 : ℝ)..R, (Y r) ^ 2) ≤ M →
    ∀ t ∈ Icc (0 : ℝ) R, Y t ≤ Y 0 * Real.exp (κ * M) :=
  @ac_cubic_uniform_of_square_integral

-- Literal nonnegative extended integral over the FULL open terminal window.
example (Y : ℝ → ℝ) (b : ℝ) :
    stoppedSquareBudget Y b =
      ∫⁻ r in Ioo (0 : ℝ) b, ENNReal.ofReal ((Y r) ^ 2) := rfl

example : ∀ Y : ℝ → ℝ, stoppedSquareBudget Y 0 = 0 :=
  stoppedSquareBudget_zero_window

example : ∀ b : ℝ, stoppedSquareBudget (fun _ : ℝ => 0) b = 0 :=
  stoppedSquareBudget_zero_function

example : ∀ {Y : ℝ → ℝ} {t b : ℝ}, 0 ≤ t → t < b →
    ContinuousOn Y (Icc (0 : ℝ) t) →
    (∫⁻ r in Ioo (0 : ℝ) b, ENNReal.ofReal ((Y r) ^ 2)) ≠ ∞ →
    (∫ r in (0 : ℝ)..t, (Y r) ^ 2) ≤
      (∫⁻ r in Ioo (0 : ℝ) b, ENNReal.ofReal ((Y r) ^ 2)).toReal :=
  @square_integral_le_stopped_budget

example : ∀ {Y : ℝ → ℝ} {κ b : ℝ}, 0 ≤ κ → 0 ≤ Y 0 →
    (∀ R ∈ Ico (0 : ℝ) b, AbsolutelyContinuousOnInterval Y 0 R) →
    (∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) b), deriv Y r ≤ κ * (Y r) ^ 3) →
    (∫⁻ r in Ioo (0 : ℝ) b, ENNReal.ofReal ((Y r) ^ 2)) ≠ ∞ →
    ∀ t ∈ Ico (0 : ℝ) b,
      Y t ≤ Y 0 * Real.exp (κ *
        (∫⁻ r in Ioo (0 : ℝ) b, ENNReal.ofReal ((Y r) ^ 2)).toReal) :=
  @ac_cubic_uniform_of_finite_stopped_budget

example : ∀ {Y : ℝ → ℝ} {κ b : ℝ}, 0 ≤ κ → 0 ≤ Y 0 →
    (∀ R ∈ Ico (0 : ℝ) b, AbsolutelyContinuousOnInterval Y 0 R) →
    (∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) b), deriv Y r ≤ κ * (Y r) ^ 3) →
    (∫⁻ r in Ioo (0 : ℝ) b, ENNReal.ofReal ((Y r) ^ 2)) ≠ ∞ →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico (0 : ℝ) b, Y t ≤ B :=
  @ac_cubic_bounded_of_finite_stopped_budget

end QFAACBudget.ExpectedTypes

end

-- NAMED REPORTS: generated text, executed only by authorized external CI.
#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ac_cubic_volterra"
#check @MethbokeAddon.QuasiFeffermanA.ac_cubic_volterra
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ac_cubic_volterra"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ac_cubic_volterra"
#print axioms MethbokeAddon.QuasiFeffermanA.ac_cubic_volterra
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ac_cubic_volterra"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ac_cubic_square_budget_bound"
#check @MethbokeAddon.QuasiFeffermanA.ac_cubic_square_budget_bound
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ac_cubic_square_budget_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ac_cubic_square_budget_bound"
#print axioms MethbokeAddon.QuasiFeffermanA.ac_cubic_square_budget_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ac_cubic_square_budget_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_square_integral"
#check @MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_square_integral
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_square_integral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_square_integral"
#print axioms MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_square_integral
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_square_integral"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget"
#check @MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_zero_window"
#check @MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_zero_window
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_zero_window"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_zero_window"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_zero_window
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_zero_window"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_zero_function"
#check @MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_zero_function
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_zero_function"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_zero_function"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_zero_function
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_zero_function"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.square_integral_le_stopped_budget"
#check @MethbokeAddon.QuasiFeffermanA.square_integral_le_stopped_budget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.square_integral_le_stopped_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.square_integral_le_stopped_budget"
#print axioms MethbokeAddon.QuasiFeffermanA.square_integral_le_stopped_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.square_integral_le_stopped_budget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_finite_stopped_budget"
#check @MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_finite_stopped_budget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_finite_stopped_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_finite_stopped_budget"
#print axioms MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_finite_stopped_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_finite_stopped_budget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ac_cubic_bounded_of_finite_stopped_budget"
#check @MethbokeAddon.QuasiFeffermanA.ac_cubic_bounded_of_finite_stopped_budget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ac_cubic_bounded_of_finite_stopped_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ac_cubic_bounded_of_finite_stopped_budget"
#print axioms MethbokeAddon.QuasiFeffermanA.ac_cubic_bounded_of_finite_stopped_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ac_cubic_bounded_of_finite_stopped_budget"
