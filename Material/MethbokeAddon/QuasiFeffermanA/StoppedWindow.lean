import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# An extended lifetime stopped by a finite real cutoff

The minimum is taken in `ENNReal` and proved finite before its real endpoint
is used. The observation set is exactly an open real interval, including
zero lifetimes, zero cutoffs and infinite lifetimes. No trajectory or
terminal continuity is part of this construction.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace MethbokeAddon.QuasiFeffermanA

/-- Stop in the extended nonnegative reals, before taking any real value. -/
def stoppedLifetime (T : ℝ≥0∞) (τ : ℝ) : ℝ≥0∞ :=
  min T (ENNReal.ofReal τ)

/-- A finite real cutoff makes the stopped lifetime finite, even when `T = ∞`. -/
theorem stoppedLifetime_ne_top (T : ℝ≥0∞) (τ : ℝ) :
    stoppedLifetime T τ ≠ (∞ : ℝ≥0∞) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)

/-- The real endpoint is taken only after `stoppedLifetime_ne_top`. -/
def stoppedEndpoint (T : ℝ≥0∞) (τ : ℝ) : ℝ :=
  (stoppedLifetime T τ).toReal

theorem stoppedEndpoint_nonneg (T : ℝ≥0∞) (τ : ℝ) :
    0 ≤ stoppedEndpoint T τ := ENNReal.toReal_nonneg

theorem ofReal_stoppedEndpoint (T : ℝ≥0∞) (τ : ℝ) :
    ENNReal.ofReal (stoppedEndpoint T τ) = stoppedLifetime T τ :=
  ENNReal.ofReal_toReal (stoppedLifetime_ne_top T τ)

theorem stoppedEndpoint_le_cutoff (T : ℝ≥0∞) {τ : ℝ} (hτ : 0 ≤ τ) :
    stoppedEndpoint T τ ≤ τ :=
  ENNReal.toReal_le_of_le_ofReal hτ (min_le_right _ _)

theorem stoppedEndpoint_mono {T₁ T₂ : ℝ≥0∞} {τ₁ τ₂ : ℝ}
    (hT : T₁ ≤ T₂) (hτ : τ₁ ≤ τ₂) :
    stoppedEndpoint T₁ τ₁ ≤ stoppedEndpoint T₂ τ₂ :=
  ENNReal.toReal_mono (stoppedLifetime_ne_top T₂ τ₂)
    (min_le_min hT (ENNReal.ofReal_le_ofReal hτ))

@[simp] theorem stoppedEndpoint_zero_lifetime (τ : ℝ) :
    stoppedEndpoint 0 τ = 0 := by
  simp [stoppedEndpoint, stoppedLifetime]

@[simp] theorem stoppedEndpoint_zero_cutoff (T : ℝ≥0∞) :
    stoppedEndpoint T 0 = 0 := by
  simp [stoppedEndpoint, stoppedLifetime]

theorem stoppedEndpoint_top {τ : ℝ} (hτ : 0 ≤ τ) :
    stoppedEndpoint (∞ : ℝ≥0∞) τ = τ := by
  simp [stoppedEndpoint, stoppedLifetime, ENNReal.toReal_ofReal hτ]

/-- Positive window length means that both original stopping bounds are positive. -/
theorem stoppedEndpoint_pos_iff (T : ℝ≥0∞) (τ : ℝ) :
    0 < stoppedEndpoint T τ ↔ 0 < T ∧ 0 < τ := by
  change 0 < (min T (ENNReal.ofReal τ)).toReal ↔ _
  rw [ENNReal.toReal_pos_iff]
  constructor
  · rintro ⟨h, _⟩
    exact ⟨lt_of_lt_of_le h (min_le_left _ _),
      ENNReal.ofReal_pos.mp (lt_of_lt_of_le h (min_le_right _ _))⟩
  · rintro ⟨hT, hτ⟩
    exact ⟨lt_min hT (ENNReal.ofReal_pos.mpr hτ),
      lt_top_iff_ne_top.mpr (stoppedLifetime_ne_top T τ)⟩

/-- Literal positive times lying below both the lifetime and the real cutoff. -/
def stoppedObservation (T : ℝ≥0∞) (τ : ℝ) : Set ℝ :=
  {t | 0 < t ∧ ENNReal.ofReal t < T ∧ t < τ}

/-- Exact set equality, valid also for zero and infinite extended lifetimes. -/
theorem stoppedObservation_eq_Ioo (T : ℝ≥0∞) (τ : ℝ) :
    stoppedObservation T τ = Ioo (0 : ℝ) (stoppedEndpoint T τ) := by
  ext t
  change (0 < t ∧ ENNReal.ofReal t < T ∧ t < τ) ↔
    0 < t ∧ t < stoppedEndpoint T τ
  constructor
  · rintro ⟨ht, hT, hτ⟩
    refine ⟨ht, ?_⟩
    apply (ENNReal.ofReal_lt_iff_lt_toReal ht.le (stoppedLifetime_ne_top T τ)).mp
    exact lt_min hT ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mpr hτ)
  · rintro ⟨ht, hb⟩
    have h : ENNReal.ofReal t < stoppedLifetime T τ :=
      (ENNReal.ofReal_lt_iff_lt_toReal ht.le (stoppedLifetime_ne_top T τ)).mpr hb
    exact ⟨ht, lt_of_lt_of_le h (min_le_left _ _),
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mp
        (lt_of_lt_of_le h (min_le_right _ _))⟩

theorem measurableSet_stoppedObservation (T : ℝ≥0∞) (τ : ℝ) :
    MeasurableSet (stoppedObservation T τ) := by
  rw [stoppedObservation_eq_Ioo]
  exact measurableSet_Ioo

@[simp] theorem stoppedObservation_zero_lifetime (τ : ℝ) :
    stoppedObservation 0 τ = ∅ := by
  simp [stoppedObservation_eq_Ioo]

@[simp] theorem stoppedObservation_zero_cutoff (T : ℝ≥0∞) :
    stoppedObservation T 0 = ∅ := by
  simp [stoppedObservation_eq_Ioo]

theorem stoppedObservation_top {τ : ℝ} (hτ : 0 ≤ τ) :
    stoppedObservation (∞ : ℝ≥0∞) τ = Ioo (0 : ℝ) τ := by
  rw [stoppedObservation_eq_Ioo, stoppedEndpoint_top hτ]

theorem stoppedObservation_mono {T₁ T₂ : ℝ≥0∞} {τ₁ τ₂ : ℝ}
    (hT : T₁ ≤ T₂) (hτ : τ₁ ≤ τ₂) :
    stoppedObservation T₁ τ₁ ⊆ stoppedObservation T₂ τ₂ := by
  rintro t ⟨ht, htT, htτ⟩
  exact ⟨ht, htT.trans_le hT, htτ.trans_le hτ⟩

/-- Every compact partial interval lies inside the existing nonnegative lifetime.
This requires no value at the stopped endpoint itself. -/
theorem Icc_subset_lifetime_of_lt_stoppedEndpoint
    {T : ℝ≥0∞} {τ r : ℝ} (hr : 0 ≤ r) (hrb : r < stoppedEndpoint T τ) :
    Icc (0 : ℝ) r ⊆ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < T} := by
  have hrT : ENNReal.ofReal r < stoppedLifetime T τ :=
    (ENNReal.ofReal_lt_iff_lt_toReal hr (stoppedLifetime_ne_top T τ)).mpr hrb
  intro t ht
  exact ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2).trans_lt
    (hrT.trans_le (min_le_left _ _))⟩

end MethbokeAddon.QuasiFeffermanA
