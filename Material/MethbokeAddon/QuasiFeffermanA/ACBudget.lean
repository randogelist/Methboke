import QFA.Endpoints.Comparison.RelativeEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Absolutely continuous cubic evolution and a full stopped square budget

This scalar layer derives its Volterra inequality from an almost-everywhere
cubic derivative inequality and absolute continuity. It then applies the
existing integral Gronwall theorem. No classical time derivative at every
point, continuous derivative field, or NSE solution is assumed to exist.

The terminal budget is an extended nonnegative integral. Its finiteness is
explicit before `toReal` is used to produce a uniform real bound. The same
bound holds on every earlier time in the open terminal window.

For NSE the intended inputs are the actual enstrophy and its physical AC
inequality. Their construction, the sharp coefficient, and continuation are
separate obligations. This file proves scalar implications only.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory Filter
open scoped Interval ENNReal

namespace MethbokeAddon.QuasiFeffermanA

/-- Absolute continuity converts an a.e. cubic derivative bound into the
Volterra inequality on every closed subinterval. No endpoint derivative is
required. The coefficient may have either sign at this step. -/
theorem ac_cubic_volterra
    {Y : ℝ → ℝ} {κ R : ℝ} (hR : 0 ≤ R)
    (hY : AbsolutelyContinuousOnInterval Y 0 R)
    (hcubic : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      deriv Y r ≤ κ * (Y r) ^ 3) :
    ∀ t ∈ Icc (0 : ℝ) R,
      Y t ≤ Y 0 + ∫ r in (0 : ℝ)..t, κ * (Y r) ^ 3 := by
  have hcont : ContinuousOn Y (Icc (0 : ℝ) R) := by
    simpa only [uIcc_of_le hR] using hY.continuousOn
  intro t ht
  have hYt : AbsolutelyContinuousOnInterval Y 0 t := by
    apply hY.mono
    rw [uIcc_of_le ht.1, uIcc_of_le hR]
    exact Icc_subset_Icc le_rfl ht.2
  have hcubic_oo : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) t),
      deriv Y r ≤ κ * (Y r) ^ 3 :=
    hcubic.filter_mono (ae_mono
      (Measure.restrict_mono (Ioo_subset_Ioo le_rfl ht.2) le_rfl))
  have hcubic_cc : ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) t),
      deriv Y r ≤ κ * (Y r) ^ 3 :=
    (ae_restrict_congr_set
      (Ioo_ae_eq_Icc : Ioo (0 : ℝ) t =ᵐ[volume] Icc (0 : ℝ) t)).mp hcubic_oo
  have hpoly : IntervalIntegrable (fun r => κ * (Y r) ^ 3) volume 0 t :=
    (continuousOn_const.mul
      ((hcont.mono (Icc_subset_Icc le_rfl ht.2)).pow 3)).intervalIntegrable_of_Icc ht.1
  have hmono := intervalIntegral.integral_mono_ae_restrict ht.1
    hYt.intervalIntegrable_deriv hpoly hcubic_cc
  rw [hYt.integral_deriv_eq_sub] at hmono
  linarith

/-- Integral Gronwall controls an AC cubic evolution by its accumulated square.
The a.e. differential inequality is the input; the integral inequality is proved. -/
theorem ac_cubic_square_budget_bound
    {Y : ℝ → ℝ} {κ R : ℝ} (hR : 0 ≤ R) (hκ : 0 ≤ κ)
    (hY : AbsolutelyContinuousOnInterval Y 0 R)
    (hcubic : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      deriv Y r ≤ κ * (Y r) ^ 3) :
    ∀ t ∈ Icc (0 : ℝ) R,
      Y t ≤ Y 0 * Real.exp (κ * ∫ r in (0 : ℝ)..t, (Y r) ^ 2) := by
  have hcont : ContinuousOn Y (Icc (0 : ℝ) R) := by
    simpa only [uIcc_of_le hR] using hY.continuousOn
  have hcoef : ContinuousOn (fun r => κ * (Y r) ^ 2) (Icc (0 : ℝ) R) :=
    continuousOn_const.mul (hcont.pow 2)
  have hprod : IntervalIntegrable (fun r => (κ * (Y r) ^ 2) * Y r) volume 0 R :=
    (hcoef.mul hcont).intervalIntegrable_of_Icc hR
  have hidentity : (fun r : ℝ => (κ * (Y r) ^ 2) * Y r) =
      (fun r : ℝ => κ * (Y r) ^ 3) := by
    funext r
    ring
  have hrelative : ∀ t ∈ Icc (0 : ℝ) R,
      Y t ≤ Y 0 + ∫ r in (0 : ℝ)..t, (κ * (Y r) ^ 2) * Y r := by
    simpa only [hidentity] using ac_cubic_volterra hR hY hcubic
  have hbound := QFA.Endpoints.Comparison.CRITICAL_RELATIVE_ENERGY_GRONWALL
    hR hcoef (fun r _ => mul_nonneg hκ (sq_nonneg (Y r))) hprod hrelative
  simpa only [intervalIntegral.integral_const_mul] using hbound

/-- One real square-integral bound on the closed slab gives a uniform bound
throughout that slab. Only the initial value needs a sign assumption. -/
theorem ac_cubic_uniform_of_square_integral
    {Y : ℝ → ℝ} {κ R M : ℝ} (hR : 0 ≤ R) (hκ : 0 ≤ κ)
    (hY : AbsolutelyContinuousOnInterval Y 0 R) (hY0 : 0 ≤ Y 0)
    (hcubic : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      deriv Y r ≤ κ * (Y r) ^ 3)
    (hbudget : (∫ r in (0 : ℝ)..R, (Y r) ^ 2) ≤ M) :
    ∀ t ∈ Icc (0 : ℝ) R, Y t ≤ Y 0 * Real.exp (κ * M) := by
  have hcont : ContinuousOn Y (Icc (0 : ℝ) R) := by
    simpa only [uIcc_of_le hR] using hY.continuousOn
  have hint : IntervalIntegrable (fun r => (Y r) ^ 2) volume 0 R :=
    (hcont.pow 2).intervalIntegrable_of_Icc hR
  intro t ht
  have hprefix : (∫ r in (0 : ℝ)..t, (Y r) ^ 2) ≤ M :=
    (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Eventually.of_forall (fun r => sq_nonneg (Y r))) hint).trans hbudget
  exact (ac_cubic_square_budget_bound hR hκ hY hcubic t ht).trans
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hprefix hκ)) hY0)

/-- The full nonnegative square budget up to a real stopping time. Infinity
is retained; there is no `toReal` in the definition. -/
def stoppedSquareBudget (Y : ℝ → ℝ) (b : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioo (0 : ℝ) b, ENNReal.ofReal ((Y r) ^ 2)

@[simp] theorem stoppedSquareBudget_zero_window (Y : ℝ → ℝ) :
    stoppedSquareBudget Y 0 = 0 := by
  simp [stoppedSquareBudget]

@[simp] theorem stoppedSquareBudget_zero_function (b : ℝ) :
    stoppedSquareBudget (fun _ : ℝ => 0) b = 0 := by
  simp [stoppedSquareBudget]

/-- Finiteness of the full stopped budget controls every earlier ordinary
square integral. The explicit finiteness premise justifies `toReal`. -/
theorem square_integral_le_stopped_budget
    {Y : ℝ → ℝ} {t b : ℝ} (ht : 0 ≤ t) (htb : t < b)
    (hY : ContinuousOn Y (Icc (0 : ℝ) t))
    (hbudget : stoppedSquareBudget Y b ≠ ∞) :
    (∫ r in (0 : ℝ)..t, (Y r) ^ 2) ≤ (stoppedSquareBudget Y b).toReal := by
  have hint : IntervalIntegrable (fun r => (Y r) ^ 2) volume 0 t :=
    (hY.pow 2).intervalIntegrable_of_Icc ht
  have hidentity : ENNReal.ofReal (∫ r in (0 : ℝ)..t, (Y r) ^ 2) =
      ∫⁻ r in Ioc (0 : ℝ) t, ENNReal.ofReal ((Y r) ^ 2) := by
    rw [intervalIntegral.integral_of_le ht]
    exact ofReal_integral_eq_lintegral_ofReal hint.1
      (Eventually.of_forall (fun r => sq_nonneg (Y r)))
  have hle : ENNReal.ofReal (∫ r in (0 : ℝ)..t, (Y r) ^ 2) ≤
      stoppedSquareBudget Y b := by
    rw [hidentity]
    exact lintegral_mono_set (fun r hr => ⟨hr.1, hr.2.trans_lt htb⟩)
  have hreal := ENNReal.toReal_mono hbudget hle
  rw [ENNReal.toReal_ofReal
    (intervalIntegral.integral_nonneg_of_forall ht (fun r => sq_nonneg (Y r)))] at hreal
  exact hreal

/-- A finite full terminal budget gives one bound valid at every earlier time.
Only closed-subinterval AC is assumed; no endpoint regularity at `b` is imposed. -/
theorem ac_cubic_uniform_of_finite_stopped_budget
    {Y : ℝ → ℝ} {κ b : ℝ} (hκ : 0 ≤ κ) (hY0 : 0 ≤ Y 0)
    (hY : ∀ R ∈ Ico (0 : ℝ) b, AbsolutelyContinuousOnInterval Y 0 R)
    (hcubic : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) b),
      deriv Y r ≤ κ * (Y r) ^ 3)
    (hbudget : stoppedSquareBudget Y b ≠ ∞) :
    ∀ t ∈ Ico (0 : ℝ) b,
      Y t ≤ Y 0 * Real.exp (κ * (stoppedSquareBudget Y b).toReal) := by
  intro t ht
  have hYt := hY t ht
  have hcont : ContinuousOn Y (Icc (0 : ℝ) t) := by
    simpa only [uIcc_of_le ht.1] using hYt.continuousOn
  have hcubic_t : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) t),
      deriv Y r ≤ κ * (Y r) ^ 3 :=
    hcubic.filter_mono (ae_mono
      (Measure.restrict_mono (Ioo_subset_Ioo le_rfl ht.2.le) le_rfl))
  have hprefix := square_integral_le_stopped_budget ht.1 ht.2 hcont hbudget
  exact ac_cubic_uniform_of_square_integral ht.1 hκ hYt hY0 hcubic_t hprefix
    t ⟨ht.1, le_rfl⟩

/-- Existential form of the uniform preterminal scalar bound. It still retains
the full-budget and actual scalar evolution premises. -/
theorem ac_cubic_bounded_of_finite_stopped_budget
    {Y : ℝ → ℝ} {κ b : ℝ} (hκ : 0 ≤ κ) (hY0 : 0 ≤ Y 0)
    (hY : ∀ R ∈ Ico (0 : ℝ) b, AbsolutelyContinuousOnInterval Y 0 R)
    (hcubic : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) b),
      deriv Y r ≤ κ * (Y r) ^ 3)
    (hbudget : stoppedSquareBudget Y b ≠ ∞) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico (0 : ℝ) b, Y t ≤ B := by
  refine ⟨Y 0 * Real.exp (κ * (stoppedSquareBudget Y b).toReal),
    mul_nonneg hY0 (Real.exp_pos _).le, ?_⟩
  exact ac_cubic_uniform_of_finite_stopped_budget hκ hY0 hY hcubic hbudget

end MethbokeAddon.QuasiFeffermanA
