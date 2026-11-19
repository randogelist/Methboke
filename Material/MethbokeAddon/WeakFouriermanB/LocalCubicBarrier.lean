import SingularClosure.CubicBudget
import Mathlib.Analysis.Calculus.MeanValue

/-!
A cubic differential inequality has a short-time bound determined only by
its cubic coefficient and its initial upper bound. The affine comparison
barrier produces the square budget used in the subsequent dissipation
estimate; no square-budget or continuation premise is assumed.

Prepared for cached external verification. No local Lean execution.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Interval

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

def localCubicTime (κ R : ℝ) : ℝ :=
  1 / (16 * (κ + 1) * (R + 1) ^ 2)

theorem localCubicTime_pos {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 ≤ R) :
    0 < localCubicTime κ R := by
  unfold localCubicTime
  positivity

/-- The right derivative at the initial time suffices for the affine fence.
The time and initial bounds contain no information about higher derivatives.
-/
theorem cubic_short_time_barrier
    {y d : ℝ → ℝ} {κ R T : ℝ}
    (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (htime : T ≤ localCubicTime κ R)
    (hy : ContinuousOn y (Icc 0 T)) (hinit : y 0 ≤ R)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt y (d t) (Ici 0) t)
    (hcubic : ∀ t ∈ Ico 0 T, d t ≤ κ * (y t) ^ 3) :
    ∀ t ∈ Icc 0 T, y t ≤ 2 * (R + 1) := by
  let L : ℝ := 8 * (κ + 1) * (R + 1) ^ 3
  have hR1 : 0 < R + 1 := by linarith
  have hκ1 : 0 < κ + 1 := by linarith
  have hL : 0 < L := by dsimp [L]; positivity
  have hLtime : L * localCubicTime κ R = (R + 1) / 2 := by
    dsimp [L, localCubicTime]
    field_simp [ne_of_gt hκ1, ne_of_gt hR1]
    <;> ring
  have hfence_bound : ∀ t ∈ Icc 0 T,
      R + 1 + L * t ≤ 2 * (R + 1) := by
    intro t ht
    have hmul := mul_le_mul_of_nonneg_left (ht.2.trans htime) hL.le
    rw [hLtime] at hmul
    linarith
  have hfence : ∀ t ∈ Icc 0 T, y t ≤ R + 1 + L * t := by
    intro t ht
    refine image_le_of_deriv_right_lt_deriv_boundary
      (f' := d) (B := fun r => R + 1 + L * r) (B' := fun _ => L)
      hy ?_ ?_ ?_ ?_ ht
    · intro r hr
      exact (hderiv r hr).mono (fun s hs => hr.1.trans hs)
    · simpa only [mul_zero, add_zero] using hinit.trans (by linarith : R ≤ R + 1)
    · intro r
      simpa only [mul_one, id_eq] using!
        ((hasDerivAt_id r).const_mul L).const_add (R + 1)
    · intro r hr heq
      have hnonneg : 0 ≤ R + 1 + L * r :=
        add_nonneg hR1.le (mul_nonneg hL.le hr.1)
      have hcube := pow_le_pow_left₀ hnonneg (hfence_bound r ⟨hr.1, hr.2.le⟩) 3
      have hstrict : κ * (2 * (R + 1)) ^ 3 < L := by
        dsimp [L]
        nlinarith [pow_pos hR1 3]
      calc
        d r ≤ κ * (y r) ^ 3 := hcubic r hr
        _ = κ * (R + 1 + L * r) ^ 3 := by rw [heq]
        _ ≤ κ * (2 * (R + 1)) ^ 3 := mul_le_mul_of_nonneg_left hcube hκ
        _ < L := hstrict
  intro t ht
  exact (hfence t ht).trans (hfence_bound t ht)

/-- The short-time square budget is a conclusion of the differential
inequality and initial bound. -/
theorem cubic_short_time_square_budget
    {y d : ℝ → ℝ} {κ R T : ℝ}
    (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (htime : T ≤ localCubicTime κ R)
    (hy : ContinuousOn y (Icc 0 T))
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t) (hinit : y 0 ≤ R)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt y (d t) (Ici 0) t)
    (hcubic : ∀ t ∈ Ico 0 T, d t ≤ κ * (y t) ^ 3) :
    (∫ t in (0 : ℝ)..T, (y t) ^ 2) ≤ 4 * (R + 1) ^ 2 * T := by
  have hb := cubic_short_time_barrier hκ hR hT htime hy hinit hderiv hcubic
  have hpoint : ∀ t ∈ Icc 0 T, (y t) ^ 2 ≤ 4 * (R + 1) ^ 2 := by
    intro t ht
    have hsq := pow_le_pow_left₀ (hnonneg t ht) (hb t ht) 2
    nlinarith
  calc
    (∫ t in (0 : ℝ)..T, (y t) ^ 2) ≤
        ∫ _t in (0 : ℝ)..T, 4 * (R + 1) ^ 2 :=
      intervalIntegral.integral_mono_on hT
        ((hy.pow 2).intervalIntegrable_of_Icc hT) intervalIntegrable_const hpoint
    _ = 4 * (R + 1) ^ 2 * T := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      ring

/-- A short-time bound on the instantaneous energy plus accumulated
dissipation, with its square budget derived by the affine barrier. -/
theorem cubic_short_time_accumulation
    {y z d : ℝ → ℝ} {ν κ R T : ℝ}
    (hν : 0 < ν) (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (htime : T ≤ localCubicTime κ R)
    (hy : ContinuousOn y (Icc 0 T)) (hz : ContinuousOn z (Icc 0 T))
    (hd : ContinuousOn d (Icc 0 T))
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t) (hinit : y 0 ≤ R)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt y (d t) (Ici 0) t)
    (hcubic : ∀ t ∈ Ico 0 T, d t + ν * (z t) ^ 2 ≤ κ * (y t) ^ 3) :
    ∀ t ∈ Icc 0 T,
      y t + ν * (∫ s in (0 : ℝ)..t, (z s) ^ 2) ≤
        (R + 1) * Real.exp (κ * (4 * (R + 1) ^ 2 * T)) := by
  have hupper : ∀ t ∈ Ico 0 T, d t ≤ κ * (y t) ^ 3 := by
    intro t ht
    have hzpos := mul_nonneg hν.le (sq_nonneg (z t))
    linarith [hcubic t ht]
  have hbudget := cubic_short_time_square_budget
    hκ hR hT htime hy hnonneg hinit hderiv hupper
  apply SingularClosure.CUBIC_ENERGY_OF_SQUARE_BUDGET
    hν hκ hT (by positivity) hy hz hd hnonneg
    (hinit.trans (by linarith : R ≤ R + 1)) ?_ ?_ hbudget
  · intro t ht
    exact (hderiv t ⟨ht.1.le, ht.2⟩).hasDerivAt (Ici_mem_nhds ht.1)
  · intro t ht
    exact hcubic t ⟨ht.1.le, ht.2⟩

end

end MethbokeAddon.WeakFouriermanB
