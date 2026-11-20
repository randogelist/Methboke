import QFASixChargeBudget.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Interval ENNReal
open MethbokeAddon.QuasiFeffermanA

namespace SixChargeExpectedTypes

-- All sixteen public names have independently written full-type consumers.
example : ∀ (q : Fin 6 → ℝ), (∀ i, 0 ≤ q i) →
    (∑ i, (q i) ^ 2) ≤ (∑ i, q i) ^ 2 := @six_charge_sum_sq_le_sq_sum

example : ∀ q : Fin 6 → ℝ,
    (∑ i, q i) ^ 2 ≤ 6 * ∑ i, (q i) ^ 2 := @six_charge_sq_sum_le_six_sum_sq

section ArbitraryMeasure

variable {α : Type*} [MeasurableSpace α]

example : (Fin 6 → α → ℝ) → Measure α → ℝ≥0∞ := @sixChargeBudget α _

example : (Fin 6 → α → ℝ) → Measure α → ℝ≥0∞ := @totalChargeSquareBudget α _

example : ∀ (q : Fin 6 → α → ℝ) (μ : Measure α),
    (∀ᵐ t ∂μ, ∀ i, 0 ≤ q i t) →
    sixChargeBudget q μ ≤ totalChargeSquareBudget q μ := @sixChargeBudget_le_total α _

example : ∀ (q : Fin 6 → α → ℝ) (μ : Measure α),
    totalChargeSquareBudget q μ ≤ 6 * sixChargeBudget q μ :=
  @totalChargeSquareBudget_le_six α _

example : ∀ (q : Fin 6 → α → ℝ) (μ : Measure α),
    (∀ᵐ t ∂μ, ∀ i, 0 ≤ q i t) →
    (sixChargeBudget q μ ≠ ∞ ↔ totalChargeSquareBudget q μ ≠ ∞) :=
  @sixChargeBudget_finite_iff_total α _

example : ∀ (q : Fin 6 → α → ℝ) (μ : Measure α),
    (∀ i, AEMeasurable (q i) μ) →
    sixChargeBudget q μ = ∑ i, ∫⁻ t, ENNReal.ofReal ((q i t) ^ 2) ∂μ :=
  @sixChargeBudget_eq_sum_of_aemeasurable α _

example : ∀ (q : Fin 6 → α → ℝ) (μ : Measure α),
    (∀ i, AEMeasurable (q i) μ) →
    (sixChargeBudget q μ ≠ ∞ ↔
      ∀ i, (∫⁻ t, ENNReal.ofReal ((q i t) ^ 2) ∂μ) ≠ ∞) :=
  @sixChargeBudget_finite_iff_each α _

example : ∀ μ : Measure α,
    sixChargeBudget (fun (_ : Fin 6) (_ : α) => 0) μ = 0 := @sixChargeBudget_zero α _

example : ∀ q : Fin 6 → α → ℝ,
    sixChargeBudget q (0 : Measure α) = 0 := @sixChargeBudget_zero_measure α _

example : ∀ (q : Fin 6 → α → ℝ) (μ : Measure α) (Y : α → ℝ),
    (∀ᵐ t ∂μ, Y t = ∑ i, q i t) →
    totalChargeSquareBudget q μ = ∫⁻ t, ENNReal.ofReal ((Y t) ^ 2) ∂μ :=
  @totalChargeSquareBudget_eq_of_sum_ae α _

-- Literal budget-definition checks: actual full nonnegative integrals, no
-- truncation, normalization, finite-value hypothesis, or conversion to real.
example (q : Fin 6 → α → ℝ) (μ : Measure α) :
    sixChargeBudget q μ = ∫⁻ t, ENNReal.ofReal (∑ i : Fin 6, (q i t) ^ 2) ∂μ := rfl

example (q : Fin 6 → α → ℝ) (μ : Measure α) :
    totalChargeSquareBudget q μ =
      ∫⁻ t, ENNReal.ofReal ((∑ i : Fin 6, q i t) ^ 2) ∂μ := rfl

-- Expanded consumers enforce the literal factor-six integrands. The lower
-- bound retains charge nonnegativity; neither bound assumes measurability.
example (q : Fin 6 → α → ℝ) (μ : Measure α)
    (hq : ∀ᵐ t ∂μ, ∀ i, 0 ≤ q i t) :
    (∫⁻ t, ENNReal.ofReal (∑ i : Fin 6, (q i t) ^ 2) ∂μ) ≤
      ∫⁻ t, ENNReal.ofReal ((∑ i : Fin 6, q i t) ^ 2) ∂μ :=
  sixChargeBudget_le_total q μ hq

example (q : Fin 6 → α → ℝ) (μ : Measure α) :
    (∫⁻ t, ENNReal.ofReal ((∑ i : Fin 6, q i t) ^ 2) ∂μ) ≤
      (6 : ℝ≥0∞) * ∫⁻ t, ENNReal.ofReal (∑ i : Fin 6, (q i t) ^ 2) ∂μ :=
  totalChargeSquareBudget_le_six q μ

end ArbitraryMeasure

example : ∀ q : Fin 6 → ℝ → ℝ,
    sixChargeBudget q (volume.restrict (Ioo (0 : ℝ) 0)) = 0 :=
  @sixChargeBudget_zero_window

example : ∀ (q : Fin 6 → ℝ → ℝ) (Y : ℝ → ℝ) (b : ℝ),
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), ∀ i, 0 ≤ q i t) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), Y t = ∑ i, q i t) →
    sixChargeBudget q (volume.restrict (Ioo (0 : ℝ) b)) ≤ stoppedSquareBudget Y b ∧
      stoppedSquareBudget Y b ≤
        6 * sixChargeBudget q (volume.restrict (Ioo (0 : ℝ) b)) :=
  @stoppedSquareBudget_six_charge_bounds

example : ∀ (q : Fin 6 → ℝ → ℝ) (Y : ℝ → ℝ) (b : ℝ),
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), ∀ i, 0 ≤ q i t) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), Y t = ∑ i, q i t) →
    (stoppedSquareBudget Y b ≠ ∞ ↔
      sixChargeBudget q (volume.restrict (Ioo (0 : ℝ) b)) ≠ ∞) :=
  @stoppedSquareBudget_finite_iff_six_charge

example : ∀ (q : Fin 6 → ℝ → ℝ) {Y : ℝ → ℝ} {κ b : ℝ},
    0 ≤ κ → 0 ≤ Y 0 →
    (∀ R ∈ Ico (0 : ℝ) b, AbsolutelyContinuousOnInterval Y 0 R) →
    (∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) b), deriv Y r ≤ κ * (Y r) ^ 3) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), ∀ i, 0 ≤ q i t) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), Y t = ∑ i, q i t) →
    sixChargeBudget q (volume.restrict (Ioo (0 : ℝ) b)) ≠ ∞ →
    ∀ t ∈ Ico (0 : ℝ) b,
      Y t ≤ Y 0 * Real.exp
        (κ * (6 * (sixChargeBudget q (volume.restrict (Ioo (0 : ℝ) b))).toReal)) :=
  @ac_cubic_uniform_of_finite_six_charge_budget

-- Literal terminal-window equivalence. Charge additivity is an explicit
-- hypothesis; no physical projector/gradient identity is manufactured here.
example (q : Fin 6 → ℝ → ℝ) (Y : ℝ → ℝ) (b : ℝ)
    (hq : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), ∀ i, 0 ≤ q i t)
    (hY : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), Y t = ∑ i, q i t) :
    (∫⁻ t in Ioo (0 : ℝ) b, ENNReal.ofReal ((Y t) ^ 2)) ≠ ∞ ↔
      (∫⁻ t in Ioo (0 : ℝ) b, ENNReal.ofReal (∑ i : Fin 6, (q i t) ^ 2)) ≠ ∞ :=
  stoppedSquareBudget_finite_iff_six_charge q Y b hq hY

end SixChargeExpectedTypes

end

-- NAMED REPORTS: generated text, executed only by authorized external CI.
#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.six_charge_sum_sq_le_sq_sum"
#check @MethbokeAddon.QuasiFeffermanA.six_charge_sum_sq_le_sq_sum
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.six_charge_sum_sq_le_sq_sum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.six_charge_sum_sq_le_sq_sum"
#print axioms MethbokeAddon.QuasiFeffermanA.six_charge_sum_sq_le_sq_sum
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.six_charge_sum_sq_le_sq_sum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.six_charge_sq_sum_le_six_sum_sq"
#check @MethbokeAddon.QuasiFeffermanA.six_charge_sq_sum_le_six_sum_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.six_charge_sq_sum_le_six_sum_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.six_charge_sq_sum_le_six_sum_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.six_charge_sq_sum_le_six_sum_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.six_charge_sq_sum_le_six_sum_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget"
#check @MethbokeAddon.QuasiFeffermanA.sixChargeBudget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget"
#print axioms MethbokeAddon.QuasiFeffermanA.sixChargeBudget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget"
#check @MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget"
#print axioms MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_le_total"
#check @MethbokeAddon.QuasiFeffermanA.sixChargeBudget_le_total
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_le_total"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_le_total"
#print axioms MethbokeAddon.QuasiFeffermanA.sixChargeBudget_le_total
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_le_total"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget_le_six"
#check @MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget_le_six
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget_le_six"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget_le_six"
#print axioms MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget_le_six
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget_le_six"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_finite_iff_total"
#check @MethbokeAddon.QuasiFeffermanA.sixChargeBudget_finite_iff_total
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_finite_iff_total"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_finite_iff_total"
#print axioms MethbokeAddon.QuasiFeffermanA.sixChargeBudget_finite_iff_total
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_finite_iff_total"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_eq_sum_of_aemeasurable"
#check @MethbokeAddon.QuasiFeffermanA.sixChargeBudget_eq_sum_of_aemeasurable
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_eq_sum_of_aemeasurable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_eq_sum_of_aemeasurable"
#print axioms MethbokeAddon.QuasiFeffermanA.sixChargeBudget_eq_sum_of_aemeasurable
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_eq_sum_of_aemeasurable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_finite_iff_each"
#check @MethbokeAddon.QuasiFeffermanA.sixChargeBudget_finite_iff_each
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_finite_iff_each"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_finite_iff_each"
#print axioms MethbokeAddon.QuasiFeffermanA.sixChargeBudget_finite_iff_each
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_finite_iff_each"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero"
#check @MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero_measure"
#check @MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero_measure
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero_measure"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero_measure"
#print axioms MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero_measure
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero_measure"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget_eq_of_sum_ae"
#check @MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget_eq_of_sum_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget_eq_of_sum_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget_eq_of_sum_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget_eq_of_sum_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.totalChargeSquareBudget_eq_of_sum_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero_window"
#check @MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero_window
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero_window"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero_window"
#print axioms MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero_window
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixChargeBudget_zero_window"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_six_charge_bounds"
#check @MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_six_charge_bounds
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_six_charge_bounds"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_six_charge_bounds"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_six_charge_bounds
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_six_charge_bounds"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_finite_iff_six_charge"
#check @MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_finite_iff_six_charge
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_finite_iff_six_charge"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_finite_iff_six_charge"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_finite_iff_six_charge
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedSquareBudget_finite_iff_six_charge"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_finite_six_charge_budget"
#check @MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_finite_six_charge_budget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_finite_six_charge_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_finite_six_charge_budget"
#print axioms MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_finite_six_charge_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ac_cubic_uniform_of_finite_six_charge_budget"
