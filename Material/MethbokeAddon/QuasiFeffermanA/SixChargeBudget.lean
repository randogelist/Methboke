import MethbokeAddon.QuasiFeffermanA.ACBudget

/-!
# Six nonnegative charges and their full extended budgets

The factor-six comparison is proved from finite Cauchy--Schwarz and
nonnegative cross terms. Both budgets are extended nonnegative integrals,
so the comparison retains infinite values. The finite constant integration
rule avoids an unnecessary measurability premise for these inequalities.

The specialization to an enstrophy profile takes its almost-everywhere
charge-additivity identity explicitly. Constructing the actual physical
six projections and proving that identity are separate obligations.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Interval ENNReal

namespace MethbokeAddon.QuasiFeffermanA

/-- Nonnegative charges have nonnegative cross terms. -/
theorem six_charge_sum_sq_le_sq_sum (q : Fin 6 → ℝ)
    (hq : ∀ i, 0 ≤ q i) :
    (∑ i, (q i) ^ 2) ≤ (∑ i, q i) ^ 2 := by
  simpa using Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset (Fin 6))) (f := q) (fun i _ => hq i)

/-- Finite Cauchy--Schwarz supplies the actual coefficient six. -/
theorem six_charge_sq_sum_le_six_sum_sq (q : Fin 6 → ℝ) :
    (∑ i, q i) ^ 2 ≤ 6 * ∑ i, (q i) ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin 6)) (fun _ => (1 : ℝ)) q

section ArbitraryMeasure

variable {α : Type*} [MeasurableSpace α]

/-- Full integrated sum of the six squared real charges. -/
def sixChargeBudget (q : Fin 6 → α → ℝ) (μ : Measure α) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (∑ i, (q i t) ^ 2) ∂μ

/-- Full integrated square of the total real charge. -/
def totalChargeSquareBudget (q : Fin 6 → α → ℝ) (μ : Measure α) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal ((∑ i, q i t) ^ 2) ∂μ

/-- The lower budget comparison needs only almost-everywhere nonnegativity. -/
theorem sixChargeBudget_le_total (q : Fin 6 → α → ℝ) (μ : Measure α)
    (hq : ∀ᵐ t ∂μ, ∀ i, 0 ≤ q i t) :
    sixChargeBudget q μ ≤ totalChargeSquareBudget q μ := by
  apply lintegral_mono_ae
  filter_upwards [hq] with t ht
  exact ENNReal.ofReal_le_ofReal (six_charge_sum_sq_le_sq_sum (fun i => q i t) ht)

/-- The upper comparison is valid for arbitrary real charges and arbitrary
measures, including infinite budgets and nonmeasurable charge functions. -/
theorem totalChargeSquareBudget_le_six (q : Fin 6 → α → ℝ) (μ : Measure α) :
    totalChargeSquareBudget q μ ≤ 6 * sixChargeBudget q μ := by
  unfold totalChargeSquareBudget sixChargeBudget
  calc
    (∫⁻ t, ENNReal.ofReal ((∑ i, q i t) ^ 2) ∂μ)
        ≤ ∫⁻ t, ENNReal.ofReal (6 * ∑ i, (q i t) ^ 2) ∂μ := by
          exact lintegral_mono (fun t => ENNReal.ofReal_le_ofReal
            (six_charge_sq_sum_le_six_sum_sq (fun i => q i t)))
    _ = ∫⁻ t, (6 : ℝ≥0∞) * ENNReal.ofReal (∑ i, (q i t) ^ 2) ∂μ := by
      apply lintegral_congr
      intro t
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
      norm_num
    _ = (6 : ℝ≥0∞) * (∫⁻ t, ENNReal.ofReal (∑ i, (q i t) ^ 2) ∂μ) :=
      lintegral_const_mul' 6 _ (by norm_num)

/-- Finiteness of the two full budgets is equivalent. -/
theorem sixChargeBudget_finite_iff_total (q : Fin 6 → α → ℝ) (μ : Measure α)
    (hq : ∀ᵐ t ∂μ, ∀ i, 0 ≤ q i t) :
    sixChargeBudget q μ ≠ ∞ ↔ totalChargeSquareBudget q μ ≠ ∞ := by
  constructor
  · intro hfinite
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num : (6 : ℝ≥0∞) ≠ ∞) hfinite)
      (totalChargeSquareBudget_le_six q μ)
  · intro hfinite
    exact ne_top_of_le_ne_top hfinite (sixChargeBudget_le_total q μ hq)

/-- With measurable charges the full aggregate budget is the finite sum of
individual full budgets. No finite-value assumption is needed. -/
theorem sixChargeBudget_eq_sum_of_aemeasurable (q : Fin 6 → α → ℝ) (μ : Measure α)
    (hq : ∀ i, AEMeasurable (q i) μ) :
    sixChargeBudget q μ = ∑ i, ∫⁻ t, ENNReal.ofReal ((q i t) ^ 2) ∂μ := by
  unfold sixChargeBudget
  have hsplit (t : α) : ENNReal.ofReal (∑ i, (q i t) ^ 2) =
      ∑ i, ENNReal.ofReal ((q i t) ^ 2) :=
    ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (q i t))
  simp_rw [hsplit]
  exact lintegral_finsetSum' Finset.univ
    (fun i _ => ((hq i).pow_const 2).ennreal_ofReal)

/-- All six individual full budgets are finite exactly when their aggregate
is finite; measurability supplies the exact finite-sum identity. -/
theorem sixChargeBudget_finite_iff_each (q : Fin 6 → α → ℝ) (μ : Measure α)
    (hq : ∀ i, AEMeasurable (q i) μ) :
    sixChargeBudget q μ ≠ ∞ ↔
      ∀ i, (∫⁻ t, ENNReal.ofReal ((q i t) ^ 2) ∂μ) ≠ ∞ := by
  rw [sixChargeBudget_eq_sum_of_aemeasurable q μ hq]
  simp only [ENNReal.sum_ne_top, Finset.mem_univ, true_implies]

@[simp] theorem sixChargeBudget_zero (μ : Measure α) :
    sixChargeBudget (fun (_ : Fin 6) (_ : α) => 0) μ = 0 := by
  simp [sixChargeBudget]

@[simp] theorem sixChargeBudget_zero_measure (q : Fin 6 → α → ℝ) :
    sixChargeBudget q (0 : Measure α) = 0 := by
  simp [sixChargeBudget]

/-- An explicitly supplied same-path charge identity identifies the total
budget with the given scalar profile. This does not construct projectors. -/
theorem totalChargeSquareBudget_eq_of_sum_ae
    (q : Fin 6 → α → ℝ) (μ : Measure α) (Y : α → ℝ)
    (hY : ∀ᵐ t ∂μ, Y t = ∑ i, q i t) :
    totalChargeSquareBudget q μ = ∫⁻ t, ENNReal.ofReal ((Y t) ^ 2) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [hY] with t ht
  rw [ht]

end ArbitraryMeasure

/-- The empty stopped window has zero six-charge budget. -/
@[simp] theorem sixChargeBudget_zero_window (q : Fin 6 → ℝ → ℝ) :
    sixChargeBudget q (volume.restrict (Ioo (0 : ℝ) 0)) = 0 := by
  simp

/-- The physical-profile specialization keeps nonnegativity and actual
charge additivity explicit, and preserves the whole stopped window. -/
theorem stoppedSquareBudget_six_charge_bounds
    (q : Fin 6 → ℝ → ℝ) (Y : ℝ → ℝ) (b : ℝ)
    (hq : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), ∀ i, 0 ≤ q i t)
    (hY : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), Y t = ∑ i, q i t) :
    sixChargeBudget q (volume.restrict (Ioo (0 : ℝ) b)) ≤ stoppedSquareBudget Y b ∧
      stoppedSquareBudget Y b ≤ 6 * sixChargeBudget q (volume.restrict (Ioo (0 : ℝ) b)) := by
  have heq : totalChargeSquareBudget q (volume.restrict (Ioo (0 : ℝ) b)) =
      stoppedSquareBudget Y b :=
    totalChargeSquareBudget_eq_of_sum_ae q (volume.restrict (Ioo (0 : ℝ) b)) Y hY
  rw [← heq]
  exact ⟨sixChargeBudget_le_total q _ hq, totalChargeSquareBudget_le_six q _⟩

/-- Exact finiteness equivalence for a supplied charge-additive scalar profile. -/
theorem stoppedSquareBudget_finite_iff_six_charge
    (q : Fin 6 → ℝ → ℝ) (Y : ℝ → ℝ) (b : ℝ)
    (hq : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), ∀ i, 0 ≤ q i t)
    (hY : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), Y t = ∑ i, q i t) :
    stoppedSquareBudget Y b ≠ ∞ ↔
      sixChargeBudget q (volume.restrict (Ioo (0 : ℝ) b)) ≠ ∞ := by
  have heq : totalChargeSquareBudget q (volume.restrict (Ioo (0 : ℝ) b)) =
      stoppedSquareBudget Y b :=
    totalChargeSquareBudget_eq_of_sum_ae q (volume.restrict (Ioo (0 : ℝ) b)) Y hY
  rw [← heq]
  exact (sixChargeBudget_finite_iff_total q _ hq).symm

/-- The scalar AC/cubic route with a finite full six-charge budget gives an
explicit factor-six exponential bound at every preterminal time. Actual
charge additivity and actual scalar evolution remain hypotheses. -/
theorem ac_cubic_uniform_of_finite_six_charge_budget
    (q : Fin 6 → ℝ → ℝ) {Y : ℝ → ℝ} {κ b : ℝ}
    (hκ : 0 ≤ κ) (hY0 : 0 ≤ Y 0)
    (hAC : ∀ R ∈ Ico (0 : ℝ) b, AbsolutelyContinuousOnInterval Y 0 R)
    (hcubic : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) b),
      deriv Y r ≤ κ * (Y r) ^ 3)
    (hq : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), ∀ i, 0 ≤ q i t)
    (hY : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), Y t = ∑ i, q i t)
    (hbudget : sixChargeBudget q (volume.restrict (Ioo (0 : ℝ) b)) ≠ ∞) :
    ∀ t ∈ Ico (0 : ℝ) b,
      Y t ≤ Y 0 * Real.exp
        (κ * (6 * (sixChargeBudget q (volume.restrict (Ioo (0 : ℝ) b))).toReal)) := by
  have hfinite : stoppedSquareBudget Y b ≠ ∞ :=
    (stoppedSquareBudget_finite_iff_six_charge q Y b hq hY).mpr hbudget
  have hreal : (stoppedSquareBudget Y b).toReal ≤
      6 * (sixChargeBudget q (volume.restrict (Ioo (0 : ℝ) b))).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num : (6 : ℝ≥0∞) ≠ ∞) hbudget)
      (stoppedSquareBudget_six_charge_bounds q Y b hq hY).2
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using h
  intro t ht
  exact (ac_cubic_uniform_of_finite_stopped_budget hκ hY0 hAC hcubic hfinite t ht).trans
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hreal hκ)) hY0)

end MethbokeAddon.QuasiFeffermanA
