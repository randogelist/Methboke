import QFA.Endpoints.Energy.ProductBudget
import QFA.Endpoints.GoodTime.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# QFA scalar cutoff and admissible good times

The parameter `S` is an arbitrary positive real number. This module does not
assert that it is a Sobolev constant. The actual spatial estimate, the physical
energy profile and the interpretation of `Good` as a valid NSE restart remain
separate obligations.

The cutoff has a factor of two of averaging slack. For nonzero `M`, the weighted
energy budget therefore gives a good time strictly before the cutoff. Markov's
inequality also leaves at least half of the observation interval in the strict
subcritical set, even after retaining the supplied a.e. predicate `Good`.

The zero cutoff is recorded separately. No positive-time selector is applied
when `M = 0`; the physical zero-datum rigidity argument belongs to the energy
and solution-class layer.

Prepared source only. Matching authorized external compiler and exact
declaration-level axiom evidence are required before acceptance. No local Lean,
Lake, kernel audit or project runner is used to prepare this file.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Interval

namespace MethbokeAddon.QuasiFeffermanA

noncomputable section

/-- Scalar product threshold; no spatial inequality is built into this definition. -/
def productThreshold (S ν : ℝ) : ℝ := ν ^ 4 / S ^ 6

/-- Safe averaging cutoff for an initial L2 norm `M`. -/
def safeCutoff (S M ν : ℝ) : ℝ := S ^ 6 * M ^ 4 / (2 * ν ^ 5)

theorem productThreshold_pos {S ν : ℝ} (hS : 0 < S) (hν : 0 < ν) :
    0 < productThreshold S ν := by
  unfold productThreshold
  positivity

theorem safeCutoff_nonneg (S M : ℝ) {ν : ℝ} (hν : 0 < ν) :
    0 ≤ safeCutoff S M ν := by
  unfold safeCutoff
  positivity

theorem safeCutoff_pos {S M ν : ℝ}
    (hS : 0 < S) (hν : 0 < ν) (hM : M ≠ 0) :
    0 < safeCutoff S M ν := by
  have hM4 : 0 < M ^ 4 :=
    lt_of_le_of_ne (by positivity) (Ne.symm (pow_ne_zero 4 hM))
  unfold safeCutoff
  exact div_pos (mul_pos (pow_pos hS 6) hM4) (by positivity)

@[simp]
theorem safeCutoff_zero (S ν : ℝ) : safeCutoff S 0 ν = 0 := by
  simp [safeCutoff]

/-- Exact normalization of threshold times observation length. -/
theorem threshold_mul_safeCutoff {S M ν : ℝ}
    (hS : 0 < S) (hν : 0 < ν) :
    productThreshold S ν * safeCutoff S M ν = M ^ 4 / (2 * ν) := by
  unfold productThreshold safeCutoff
  field_simp [ne_of_gt hS, ne_of_gt hν] <;> ring

/-- The weighted energy budget uses only half the threshold-length product. -/
theorem budget_eq_half_threshold_cutoff {S M ν : ℝ}
    (hS : 0 < S) (hν : 0 < ν) :
    M ^ 4 / (4 * ν) = productThreshold S ν * safeCutoff S M ν / 2 := by
  rw [threshold_mul_safeCutoff hS hν]
  field_simp [ne_of_gt hν] <;> ring

/-- Nonzero data turn the half-budget identity into the strict average needed
by the existing scalar good-time selector. -/
theorem budget_lt_threshold_cutoff {S M ν : ℝ}
    (hS : 0 < S) (hν : 0 < ν) (hM : M ≠ 0) :
    M ^ 4 / (4 * ν) < productThreshold S ν * safeCutoff S M ν := by
  have hpositive : 0 < productThreshold S ν * safeCutoff S M ν :=
    mul_pos (productThreshold_pos hS hν) (safeCutoff_pos hS hν hM)
  rw [budget_eq_half_threshold_cutoff hS hν]
  linarith

/-- Conditional numerical rewrite. The sixth-power identity is a premise;
this theorem does not prove a sharp Sobolev inequality. -/
theorem safeCutoff_eq_pi_formula_of_sixth_power {S M ν : ℝ}
    (hν : 0 < ν) (hS6 : S ^ 6 = 16 / (27 * Real.pi ^ 4)) :
    safeCutoff S M ν = 8 * M ^ 4 / (27 * Real.pi ^ 4 * ν ^ 5) := by
  unfold safeCutoff
  rw [hS6]
  field_simp [ne_of_gt hν, Real.pi_ne_zero] <;> ring

/-- Select an admissible strictly subcritical time from the weighted budget.
The arbitrary full-measure predicate is retained in the selected witness. -/
theorem exists_good_time_of_product_budget
    {E D : ℝ → ℝ} {Good : ℝ → Prop} {S M ν : ℝ}
    (hS : 0 < S) (hν : 0 < ν) (hM : M ≠ 0)
    (hprod : Integrable (fun t => E t * D t)
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν))))
    (hgood : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), Good t)
    (hbudget : (∫ t in Ioo (0 : ℝ) (safeCutoff S M ν), E t * D t) ≤
      M ^ 4 / (4 * ν)) :
    ∃ s, 0 < s ∧ s < safeCutoff S M ν ∧ Good s ∧
      E s * D s < productThreshold S ν := by
  exact QFA.Endpoints.GoodTime.exists_good_time_of_integral_lt
    (f := fun t => E t * D t) (Good := Good)
    (T := safeCutoff S M ν) (c := productThreshold S ν)
    (safeCutoff_pos hS hν hM) (productThreshold_pos hS hν).le
    hprod hgood (hbudget.trans_lt (budget_lt_threshold_cutoff hS hν hM))

/-- Derive product integrability and the sharp weighted budget from the actual
scalar energy envelope before applying the selector. Only the envelope is
differentiated inside the imported theorem. -/
theorem exists_good_time_of_energy_envelope
    {E D : ℝ → ℝ} {Good : ℝ → Prop} {S M ν : ℝ}
    (hS : 0 < S) (hν : 0 < ν) (hM : M ≠ 0)
    (hD : IntervalIntegrable D volume (0 : ℝ) (safeCutoff S M ν))
    (hEm : AEStronglyMeasurable E
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν))))
    (hDnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), 0 ≤ D t)
    (hEnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), 0 ≤ E t)
    (hEF : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)),
      E t ≤ QFA.Energy.envelope M ν D t)
    (hgood : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), Good t) :
    ∃ s, 0 < s ∧ s < safeCutoff S M ν ∧ Good s ∧
      E s * D s < productThreshold S ν := by
  obtain ⟨hprod, hbudget⟩ := QFA.Energy.product_budget_Ioo
    (safeCutoff_nonneg S M hν) hν hD hEm hDnn hEnn hEF
  exact exists_good_time_of_product_budget hS hν hM hprod hgood hbudget

/-- Finite-measure Markov estimate with half-budget slack. Integrability gives
null measurability of the bad set; no pointwise continuity is required. -/
theorem subcritical_measure_ge_half
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} {c : ℝ}
    (hc : 0 < c) (hf : Integrable f μ)
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hbudget : (∫ x, f x ∂μ) ≤ c * μ.real univ / 2) :
    μ.real univ / 2 ≤ μ.real {x | f x < c} := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hf c
  have hbad : μ.real {x | c ≤ f x} ≤ μ.real univ / 2 := by
    apply (mul_le_mul_left hc).mp
    calc
      c * μ.real {x | c ≤ f x} ≤ ∫ x, f x ∂μ := hmarkov
      _ ≤ c * μ.real univ / 2 := hbudget
      _ = c * (μ.real univ / 2) := by ring
  have hmeas : NullMeasurableSet {x | c ≤ f x} μ :=
    hf.aemeasurable.nullMeasurable measurableSet_Ici
  have hsplit := measureReal_add_measureReal_compl₀ hmeas
  have hcompl : {x | c ≤ f x}ᶜ = {x | f x < c} := by
    ext x
    simp only [mem_compl_iff, mem_setOf_eq, not_le]
  rw [hcompl] at hsplit
  linarith

/-- At least half of the safe observation interval has strict product
smallness and retains the supplied a.e. predicate. The `M = 0` case is a
zero-measure statement, not a positive-time witness. -/
theorem good_set_measure_ge_half_of_product_budget
    {E D : ℝ → ℝ} {Good : ℝ → Prop} {S M ν : ℝ}
    (hS : 0 < S) (hν : 0 < ν)
    (hprod : Integrable (fun t => E t * D t)
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν))))
    (hprodnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)),
      0 ≤ E t * D t)
    (hgood : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), Good t)
    (hbudget : (∫ t in Ioo (0 : ℝ) (safeCutoff S M ν), E t * D t) ≤
      M ^ 4 / (4 * ν)) :
    safeCutoff S M ν / 2 ≤
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν))).real
        {t | Good t ∧ E t * D t < productThreshold S ν} := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν))
  have htotal : μ.real univ = safeCutoff S M ν := by
    simp [μ, Measure.real, Real.volume_Ioo, safeCutoff_nonneg S M hν]
  have hhalf : μ.real univ / 2 ≤
      μ.real {t | E t * D t < productThreshold S ν} := by
    apply subcritical_measure_ge_half (productThreshold_pos hS hν) hprod hprodnn
    calc
      (∫ t, E t * D t ∂μ) ≤ M ^ 4 / (4 * ν) := hbudget
      _ = productThreshold S ν * safeCutoff S M ν / 2 :=
        budget_eq_half_threshold_cutoff hS hν
      _ = productThreshold S ν * μ.real univ / 2 := by rw [htotal]
  have hsets : {t | Good t ∧ E t * D t < productThreshold S ν} =ᵐ[μ]
      {t | E t * D t < productThreshold S ν} := by
    filter_upwards [hgood] with t ht
    simp only [mem_setOf_eq, ht, true_and]
  have hmeasure := measureReal_congr hsets
  change safeCutoff S M ν / 2 ≤
    μ.real {t | Good t ∧ E t * D t < productThreshold S ν}
  rw [hmeasure]
  simpa only [htotal] using hhalf

/-- The energy envelope supplies both the positive-measure admissible set and
an actual admissible restart time strictly before the safe cutoff. -/
theorem good_time_and_measure_of_energy_envelope
    {E D : ℝ → ℝ} {Good : ℝ → Prop} {S M ν : ℝ}
    (hS : 0 < S) (hν : 0 < ν) (hM : M ≠ 0)
    (hD : IntervalIntegrable D volume (0 : ℝ) (safeCutoff S M ν))
    (hEm : AEStronglyMeasurable E
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν))))
    (hDnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), 0 ≤ D t)
    (hEnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), 0 ≤ E t)
    (hEF : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)),
      E t ≤ QFA.Energy.envelope M ν D t)
    (hgood : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), Good t) :
    (safeCutoff S M ν / 2 ≤
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν))).real
        {t | Good t ∧ E t * D t < productThreshold S ν}) ∧
      ∃ s, 0 < s ∧ s < safeCutoff S M ν ∧ Good s ∧
        E s * D s < productThreshold S ν := by
  obtain ⟨hprod, hbudget⟩ := QFA.Energy.product_budget_Ioo
    (safeCutoff_nonneg S M hν) hν hD hEm hDnn hEnn hEF
  have hprodnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)),
      0 ≤ E t * D t := by
    filter_upwards [hEnn, hDnn] with t hEt hDt
    exact mul_nonneg hEt hDt
  exact ⟨good_set_measure_ge_half_of_product_budget hS hν hprod hprodnn hgood hbudget,
    exists_good_time_of_product_budget hS hν hM hprod hgood hbudget⟩

end

end MethbokeAddon.QuasiFeffermanA
