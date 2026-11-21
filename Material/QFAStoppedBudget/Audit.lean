import QFAStoppedBudget.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace QFAStoppedBudget.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA

-- Exact extended stopping construction and original observation set.
example : ℝ≥0∞ → ℝ → ℝ≥0∞ := stoppedLifetime
example (T : ℝ≥0∞) (τ : ℝ) :
    stoppedLifetime T τ = min T (ENNReal.ofReal τ) := rfl
example (T : ℝ≥0∞) (τ : ℝ) :
    min T (ENNReal.ofReal τ) ≠ (∞ : ℝ≥0∞) := stoppedLifetime_ne_top T τ
example : ℝ≥0∞ → ℝ → ℝ := stoppedEndpoint
example (T : ℝ≥0∞) (τ : ℝ) :
    stoppedEndpoint T τ = (min T (ENNReal.ofReal τ)).toReal := rfl
example (T : ℝ≥0∞) (τ : ℝ) : 0 ≤ stoppedEndpoint T τ :=
  stoppedEndpoint_nonneg T τ
example (T : ℝ≥0∞) (τ : ℝ) :
    ENNReal.ofReal (stoppedEndpoint T τ) = min T (ENNReal.ofReal τ) :=
  ofReal_stoppedEndpoint T τ
example (T : ℝ≥0∞) (τ : ℝ) (hτ : 0 ≤ τ) : stoppedEndpoint T τ ≤ τ :=
  stoppedEndpoint_le_cutoff T hτ
example (T₁ T₂ : ℝ≥0∞) (τ₁ τ₂ : ℝ) (hT : T₁ ≤ T₂) (hτ : τ₁ ≤ τ₂) :
    stoppedEndpoint T₁ τ₁ ≤ stoppedEndpoint T₂ τ₂ := stoppedEndpoint_mono hT hτ
example (τ : ℝ) : stoppedEndpoint 0 τ = 0 := stoppedEndpoint_zero_lifetime τ
example (T : ℝ≥0∞) : stoppedEndpoint T 0 = 0 := stoppedEndpoint_zero_cutoff T
example (τ : ℝ) (hτ : 0 ≤ τ) : stoppedEndpoint (∞ : ℝ≥0∞) τ = τ :=
  stoppedEndpoint_top hτ
example (T : ℝ≥0∞) (τ : ℝ) :
    0 < stoppedEndpoint T τ ↔ 0 < T ∧ 0 < τ := stoppedEndpoint_pos_iff T τ
example : ℝ≥0∞ → ℝ → Set ℝ := stoppedObservation
example (T : ℝ≥0∞) (τ : ℝ) :
    stoppedObservation T τ = {t : ℝ | 0 < t ∧ ENNReal.ofReal t < T ∧ t < τ} := rfl
example (T : ℝ≥0∞) (τ : ℝ) :
    {t : ℝ | 0 < t ∧ ENNReal.ofReal t < T ∧ t < τ} =
      Ioo (0 : ℝ) (min T (ENNReal.ofReal τ)).toReal := stoppedObservation_eq_Ioo T τ
example (T : ℝ≥0∞) (τ : ℝ) : MeasurableSet (stoppedObservation T τ) :=
  measurableSet_stoppedObservation T τ
example (τ : ℝ) : stoppedObservation 0 τ = ∅ := stoppedObservation_zero_lifetime τ
example (T : ℝ≥0∞) : stoppedObservation T 0 = ∅ := stoppedObservation_zero_cutoff T
example (τ : ℝ) (hτ : 0 ≤ τ) :
    stoppedObservation (∞ : ℝ≥0∞) τ = Ioo (0 : ℝ) τ := stoppedObservation_top hτ
example (T₁ T₂ : ℝ≥0∞) (τ₁ τ₂ : ℝ) (hT : T₁ ≤ T₂) (hτ : τ₁ ≤ τ₂) :
    stoppedObservation T₁ τ₁ ⊆ stoppedObservation T₂ τ₂ := stoppedObservation_mono hT hτ
example (T : ℝ≥0∞) (τ r : ℝ) (hr : 0 ≤ r) (hrb : r < stoppedEndpoint T τ) :
    Icc (0 : ℝ) r ⊆ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < T} :=
  Icc_subset_lifetime_of_lt_stoppedEndpoint hr hrb

-- Complete nonnegative definitions: no finite-budget or temporal-regularity premise.
example : (ℝ → ℝ≥0∞) → ℝ → ℝ≥0∞ := openIntervalBudget
example (f : ℝ → ℝ≥0∞) (b : ℝ) :
    openIntervalBudget f b = ∫⁻ t in Ioo (0 : ℝ) b, f t := rfl
example : (ℝ → ℝ≥0∞) → ℝ≥0∞ → ℝ → ℝ≥0∞ := fullStoppedBudget
example (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    fullStoppedBudget f T τ =
      ∫⁻ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < T ∧ t < τ}, f t := rfl
example (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    fullStoppedBudget f T τ = openIntervalBudget f (stoppedEndpoint T τ) :=
  fullStoppedBudget_eq_openIntervalBudget f T τ
example (f : ℝ → ℝ≥0∞) : openIntervalBudget f 0 = 0 :=
  openIntervalBudget_zero_window f
example (b : ℝ) : openIntervalBudget (fun _ : ℝ => 0) b = 0 := openIntervalBudget_zero b
example (f : ℝ → ℝ≥0∞) : Monotone (openIntervalBudget f) := openIntervalBudget_mono f
example (f g : ℝ → ℝ≥0∞) (b : ℝ) (h : ∀ t, f t ≤ g t) :
    openIntervalBudget f b ≤ openIntervalBudget g b := openIntervalBudget_mono_integrand b h
example (f g : ℝ → ℝ≥0∞) (b : ℝ) (h : ∀ t ∈ Ioo (0 : ℝ) b, f t = g t) :
    openIntervalBudget f b = openIntervalBudget g b := openIntervalBudget_congr b h
example (T : ℝ≥0∞) (τ : ℝ) : fullStoppedBudget (fun _ : ℝ => 0) T τ = 0 :=
  fullStoppedBudget_zero T τ
example (f : ℝ → ℝ≥0∞) (τ : ℝ) : fullStoppedBudget f 0 τ = 0 :=
  fullStoppedBudget_zero_lifetime f τ
example (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) : fullStoppedBudget f T 0 = 0 :=
  fullStoppedBudget_zero_cutoff f T
example (f : ℝ → ℝ≥0∞) (τ : ℝ) (hτ : 0 ≤ τ) :
    fullStoppedBudget f (∞ : ℝ≥0∞) τ = openIntervalBudget f τ := fullStoppedBudget_top f hτ
example (f g : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) (h : ∀ t, f t ≤ g t) :
    fullStoppedBudget f T τ ≤ fullStoppedBudget g T τ := fullStoppedBudget_mono T τ h
example (f : ℝ → ℝ≥0∞) (T₁ T₂ : ℝ≥0∞) (τ₁ τ₂ : ℝ)
    (hT : T₁ ≤ T₂) (hτ : τ₁ ≤ τ₂) :
    fullStoppedBudget f T₁ τ₁ ≤ fullStoppedBudget f T₂ τ₂ :=
  fullStoppedBudget_mono_window f hT hτ
example (f g : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ)
    (h : ∀ t ∈ stoppedObservation T τ, f t = g t) :
    fullStoppedBudget f T τ = fullStoppedBudget g T τ := fullStoppedBudget_congr T τ h
example (f g : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ)
    (h : f =ᵐ[volume.restrict (stoppedObservation T τ)] g) :
    fullStoppedBudget f T τ = fullStoppedBudget g T τ := fullStoppedBudget_congr_ae T τ h
example (c : ℝ≥0∞) (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ)
    (hc : c ≠ (∞ : ℝ≥0∞)) :
    fullStoppedBudget (fun t => c * f t) T τ = c * fullStoppedBudget f T τ :=
  fullStoppedBudget_const_mul c f T τ hc

-- The cutoff sequence is concrete and exhaustive; it is not an assumed approximation port.
example : ℝ → ℕ → ℝ := budgetApproxEndpoint
example (b : ℝ) (n : ℕ) :
    budgetApproxEndpoint b n = b * ((n : ℝ) + 1) / ((n : ℝ) + 2) := rfl
example (b : ℝ) (n : ℕ) :
    budgetApproxEndpoint b n = b - b / ((n : ℝ) + 2) := budgetApproxEndpoint_eq_sub b n
example (n : ℕ) : budgetApproxEndpoint 0 n = 0 := budgetApproxEndpoint_zero n
example (b : ℝ) (hb : 0 ≤ b) (n : ℕ) : 0 ≤ budgetApproxEndpoint b n :=
  budgetApproxEndpoint_nonneg hb n
example (b : ℝ) (hb : 0 ≤ b) (n : ℕ) : budgetApproxEndpoint b n ≤ b :=
  budgetApproxEndpoint_le hb n
example (b : ℝ) (hb : 0 < b) (n : ℕ) : budgetApproxEndpoint b n < b :=
  budgetApproxEndpoint_lt hb n
example (b : ℝ) (hb : 0 ≤ b) : Monotone (budgetApproxEndpoint b) :=
  budgetApproxEndpoint_mono hb
example (b : ℝ) : Tendsto (budgetApproxEndpoint b) atTop (𝓝 b) :=
  tendsto_budgetApproxEndpoint b
example (b r : ℝ) (hr : r < b) : ∃ n : ℕ, r < budgetApproxEndpoint b n :=
  budgetApproxEndpoint_cofinal b hr
example (b : ℝ) (hb : 0 ≤ b) :
    (⋃ n : ℕ, Ioo (0 : ℝ) (budgetApproxEndpoint b n)) = Ioo (0 : ℝ) b :=
  iUnion_Ioo_budgetApproxEndpoint hb

-- Full suprema and literal limits preserve infinite values and require no measurability premise.
example (f : ℝ → ℝ≥0∞) (b : ℝ) (hb : 0 ≤ b) :
    openIntervalBudget f b = ⨆ n : ℕ, openIntervalBudget f (budgetApproxEndpoint b n) :=
  openIntervalBudget_eq_iSup_approx f hb
example (f : ℝ → ℝ≥0∞) (b : ℝ) (hb : 0 ≤ b) :
    openIntervalBudget f b = ⨆ r ∈ Ico (0 : ℝ) b, openIntervalBudget f r :=
  openIntervalBudget_eq_iSup_Ico f hb
example (f : ℝ → ℝ≥0∞) (b : ℝ) (hb : 0 ≤ b) :
    openIntervalBudget f b = sSup (openIntervalBudget f '' Iio b) :=
  openIntervalBudget_eq_sSup_Iio f hb
example (f : ℝ → ℝ≥0∞) (b : ℝ) (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ => openIntervalBudget f (budgetApproxEndpoint b n))
      atTop (𝓝 (openIntervalBudget f b)) := tendsto_openIntervalBudget_approx f hb
example (f : ℝ → ℝ≥0∞) (b : ℝ) (hb : 0 ≤ b) :
    Tendsto (openIntervalBudget f) (𝓝[<] b) (𝓝 (openIntervalBudget f b)) :=
  tendsto_openIntervalBudget_nhdsLT f hb
example (f : ℝ → ℝ≥0∞) (b : ℝ) (hb : 0 ≤ b) :
    openIntervalBudget f b ≠ (∞ : ℝ≥0∞) ↔
      ∃ C : ℝ≥0, ∀ r ∈ Ico (0 : ℝ) b, openIntervalBudget f r ≤ (C : ℝ≥0∞) :=
  openIntervalBudget_ne_top_iff_uniform_bound f hb
example (f : ℝ → ℝ≥0∞) (b : ℝ) (hb : 0 ≤ b) :
    openIntervalBudget f b ≠ (∞ : ℝ≥0∞) ↔
      ∃ C : ℝ≥0, ∀ n : ℕ,
        openIntervalBudget f (budgetApproxEndpoint b n) ≤ (C : ℝ≥0∞) :=
  openIntervalBudget_ne_top_iff_uniform_approx_bound f hb
example (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    fullStoppedBudget f T τ =
      ⨆ n : ℕ, openIntervalBudget f (budgetApproxEndpoint (stoppedEndpoint T τ) n) :=
  fullStoppedBudget_eq_iSup_approx f T τ
example (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    fullStoppedBudget f T τ =
      ⨆ r ∈ Ico (0 : ℝ) (stoppedEndpoint T τ), openIntervalBudget f r :=
  fullStoppedBudget_eq_iSup_Ico f T τ
example (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    Tendsto (fun n : ℕ => openIntervalBudget f
      (budgetApproxEndpoint (stoppedEndpoint T τ) n)) atTop (𝓝 (fullStoppedBudget f T τ)) :=
  tendsto_fullStoppedBudget_approx f T τ
example (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    Tendsto (openIntervalBudget f) (𝓝[<] stoppedEndpoint T τ)
      (𝓝 (fullStoppedBudget f T τ)) := tendsto_fullStoppedBudget_nhdsLT f T τ
example (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    fullStoppedBudget f T τ ≠ (∞ : ℝ≥0∞) ↔
      ∃ C : ℝ≥0, ∀ r ∈ Ico (0 : ℝ) (stoppedEndpoint T τ),
        openIntervalBudget f r ≤ (C : ℝ≥0∞) :=
  fullStoppedBudget_ne_top_iff_uniform_bound f T τ
example (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    fullStoppedBudget f T τ ≠ (∞ : ℝ≥0∞) ↔
      ∃ C : ℝ≥0, ∀ n : ℕ, openIntervalBudget f
        (budgetApproxEndpoint (stoppedEndpoint T τ) n) ≤ (C : ℝ≥0∞) :=
  fullStoppedBudget_ne_top_iff_uniform_approx_bound f T τ

-- Literal, independently expanded terminal-window statements.
example (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    Tendsto (fun r : ℝ => ∫⁻ t in Ioo (0 : ℝ) r, f t)
      (𝓝[<] (min T (ENNReal.ofReal τ)).toReal)
      (𝓝 (∫⁻ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < T ∧ t < τ}, f t)) :=
  tendsto_fullStoppedBudget_nhdsLT f T τ
example (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    (∫⁻ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < T ∧ t < τ}, f t) ≠ (∞ : ℝ≥0∞) ↔
      ∃ C : ℝ≥0, ∀ r : ℝ, (0 ≤ r ∧ r < (min T (ENNReal.ofReal τ)).toReal) →
        (∫⁻ t in Ioo (0 : ℝ) r, f t) ≤ (C : ℝ≥0∞) :=
  fullStoppedBudget_ne_top_iff_uniform_bound f T τ

-- Ordinary integrals retain genuine local integrability, with no terminal extension premise.
example (g : ℝ → ℝ) (b : ℝ) (hg : IntegrableOn g (Ioo (0 : ℝ) b) volume)
    (hgnonneg : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), 0 ≤ g t) :
    openIntervalBudget (fun t => ENNReal.ofReal (g t)) b =
      ENNReal.ofReal (∫ t in Ioo (0 : ℝ) b, g t) :=
  openIntervalBudget_ofReal_eq_integral g b hg hgnonneg
example (Y : ℝ → ℝ) (r : ℝ) (hY : ContinuousOn Y (Icc (0 : ℝ) r)) :
    openIntervalBudget (fun t => ENNReal.ofReal ((Y t) ^ 2)) r =
      ENNReal.ofReal (∫ t in Ioo (0 : ℝ) r, (Y t) ^ 2) :=
  openIntervalBudget_sq_eq_integral Y hY
example (Y : ℝ → ℝ) (r : ℝ) (hY : ContinuousOn Y (Icc (0 : ℝ) r)) :
    openIntervalBudget (fun t => ENNReal.ofReal ((Y t) ^ 2)) r ≠ (∞ : ℝ≥0∞) :=
  openIntervalBudget_sq_ne_top Y hY
example (Y : ℝ → ℝ) (r : ℝ) (hr : 0 ≤ r) (hY : ContinuousOn Y (Icc (0 : ℝ) r)) :
    openIntervalBudget (fun t => ENNReal.ofReal ((Y t) ^ 2)) r =
      ENNReal.ofReal (∫ t in (0 : ℝ)..r, (Y t) ^ 2) :=
  openIntervalBudget_sq_eq_intervalIntegral Y hr hY

end QFAStoppedBudget.ExpectedTypes

-- Ordered named full type and axiom reports; external verification only.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedLifetime"
#check @MethbokeAddon.QuasiFeffermanA.stoppedLifetime
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedLifetime"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedLifetime"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedLifetime
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedLifetime"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedLifetime_ne_top"
#check @MethbokeAddon.QuasiFeffermanA.stoppedLifetime_ne_top
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedLifetime_ne_top"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedLifetime_ne_top"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedLifetime_ne_top
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedLifetime_ne_top"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint"
#check @MethbokeAddon.QuasiFeffermanA.stoppedEndpoint
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedEndpoint
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_nonneg"
#check @MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_nonneg"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ofReal_stoppedEndpoint"
#check @MethbokeAddon.QuasiFeffermanA.ofReal_stoppedEndpoint
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ofReal_stoppedEndpoint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ofReal_stoppedEndpoint"
#print axioms MethbokeAddon.QuasiFeffermanA.ofReal_stoppedEndpoint
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ofReal_stoppedEndpoint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_le_cutoff"
#check @MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_le_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_le_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_le_cutoff"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_le_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_le_cutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_mono"
#check @MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_mono
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_mono"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_mono"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_mono
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_mono"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_zero_lifetime"
#check @MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_zero_lifetime
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_zero_lifetime"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_zero_lifetime"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_zero_lifetime
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_zero_lifetime"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_zero_cutoff"
#check @MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_zero_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_zero_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_zero_cutoff"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_zero_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_zero_cutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_top"
#check @MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_top
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_top"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_top"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_top
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_top"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_pos_iff"
#check @MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_pos_iff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_pos_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_pos_iff"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_pos_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedEndpoint_pos_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedObservation"
#check @MethbokeAddon.QuasiFeffermanA.stoppedObservation
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedObservation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedObservation"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedObservation
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedObservation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedObservation_eq_Ioo"
#check @MethbokeAddon.QuasiFeffermanA.stoppedObservation_eq_Ioo
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedObservation_eq_Ioo"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedObservation_eq_Ioo"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedObservation_eq_Ioo
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedObservation_eq_Ioo"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.measurableSet_stoppedObservation"
#check @MethbokeAddon.QuasiFeffermanA.measurableSet_stoppedObservation
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.measurableSet_stoppedObservation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.measurableSet_stoppedObservation"
#print axioms MethbokeAddon.QuasiFeffermanA.measurableSet_stoppedObservation
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.measurableSet_stoppedObservation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedObservation_zero_lifetime"
#check @MethbokeAddon.QuasiFeffermanA.stoppedObservation_zero_lifetime
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedObservation_zero_lifetime"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedObservation_zero_lifetime"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedObservation_zero_lifetime
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedObservation_zero_lifetime"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedObservation_zero_cutoff"
#check @MethbokeAddon.QuasiFeffermanA.stoppedObservation_zero_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedObservation_zero_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedObservation_zero_cutoff"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedObservation_zero_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedObservation_zero_cutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedObservation_top"
#check @MethbokeAddon.QuasiFeffermanA.stoppedObservation_top
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedObservation_top"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedObservation_top"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedObservation_top
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedObservation_top"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedObservation_mono"
#check @MethbokeAddon.QuasiFeffermanA.stoppedObservation_mono
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.stoppedObservation_mono"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.stoppedObservation_mono"
#print axioms MethbokeAddon.QuasiFeffermanA.stoppedObservation_mono
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.stoppedObservation_mono"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.Icc_subset_lifetime_of_lt_stoppedEndpoint"
#check @MethbokeAddon.QuasiFeffermanA.Icc_subset_lifetime_of_lt_stoppedEndpoint
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.Icc_subset_lifetime_of_lt_stoppedEndpoint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.Icc_subset_lifetime_of_lt_stoppedEndpoint"
#print axioms MethbokeAddon.QuasiFeffermanA.Icc_subset_lifetime_of_lt_stoppedEndpoint
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.Icc_subset_lifetime_of_lt_stoppedEndpoint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget"
#check @MethbokeAddon.QuasiFeffermanA.openIntervalBudget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget"
#print axioms MethbokeAddon.QuasiFeffermanA.openIntervalBudget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget"
#check @MethbokeAddon.QuasiFeffermanA.fullStoppedBudget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget"
#print axioms MethbokeAddon.QuasiFeffermanA.fullStoppedBudget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_openIntervalBudget"
#check @MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_openIntervalBudget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_openIntervalBudget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_openIntervalBudget"
#print axioms MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_openIntervalBudget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_openIntervalBudget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_zero_window"
#check @MethbokeAddon.QuasiFeffermanA.openIntervalBudget_zero_window
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_zero_window"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_zero_window"
#print axioms MethbokeAddon.QuasiFeffermanA.openIntervalBudget_zero_window
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_zero_window"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_zero"
#check @MethbokeAddon.QuasiFeffermanA.openIntervalBudget_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.openIntervalBudget_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_mono"
#check @MethbokeAddon.QuasiFeffermanA.openIntervalBudget_mono
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_mono"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_mono"
#print axioms MethbokeAddon.QuasiFeffermanA.openIntervalBudget_mono
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_mono"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_mono_integrand"
#check @MethbokeAddon.QuasiFeffermanA.openIntervalBudget_mono_integrand
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_mono_integrand"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_mono_integrand"
#print axioms MethbokeAddon.QuasiFeffermanA.openIntervalBudget_mono_integrand
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_mono_integrand"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_congr"
#check @MethbokeAddon.QuasiFeffermanA.openIntervalBudget_congr
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_congr"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_congr"
#print axioms MethbokeAddon.QuasiFeffermanA.openIntervalBudget_congr
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_congr"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero"
#check @MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero_lifetime"
#check @MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero_lifetime
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero_lifetime"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero_lifetime"
#print axioms MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero_lifetime
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero_lifetime"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero_cutoff"
#check @MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero_cutoff"
#print axioms MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_zero_cutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_top"
#check @MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_top
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_top"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_top"
#print axioms MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_top
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_top"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_mono"
#check @MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_mono
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_mono"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_mono"
#print axioms MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_mono
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_mono"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_mono_window"
#check @MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_mono_window
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_mono_window"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_mono_window"
#print axioms MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_mono_window
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_mono_window"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_congr"
#check @MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_congr
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_congr"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_congr"
#print axioms MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_congr
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_congr"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_congr_ae"
#check @MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_congr_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_congr_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_congr_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_congr_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_congr_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_const_mul"
#check @MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_const_mul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_const_mul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_const_mul"
#print axioms MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_const_mul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_const_mul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint"
#check @MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint"
#print axioms MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_eq_sub"
#check @MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_eq_sub
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_eq_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_eq_sub"
#print axioms MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_eq_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_eq_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_zero"
#check @MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_nonneg"
#check @MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_nonneg"
#print axioms MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_le"
#check @MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_le"
#print axioms MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_lt"
#check @MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_lt
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_lt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_lt"
#print axioms MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_lt
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_lt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_mono"
#check @MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_mono
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_mono"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_mono"
#print axioms MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_mono
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_mono"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.tendsto_budgetApproxEndpoint"
#check @MethbokeAddon.QuasiFeffermanA.tendsto_budgetApproxEndpoint
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.tendsto_budgetApproxEndpoint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.tendsto_budgetApproxEndpoint"
#print axioms MethbokeAddon.QuasiFeffermanA.tendsto_budgetApproxEndpoint
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.tendsto_budgetApproxEndpoint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_cofinal"
#check @MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_cofinal
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_cofinal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_cofinal"
#print axioms MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_cofinal
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.budgetApproxEndpoint_cofinal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.iUnion_Ioo_budgetApproxEndpoint"
#check @MethbokeAddon.QuasiFeffermanA.iUnion_Ioo_budgetApproxEndpoint
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.iUnion_Ioo_budgetApproxEndpoint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.iUnion_Ioo_budgetApproxEndpoint"
#print axioms MethbokeAddon.QuasiFeffermanA.iUnion_Ioo_budgetApproxEndpoint
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.iUnion_Ioo_budgetApproxEndpoint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_iSup_approx"
#check @MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_iSup_approx
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_iSup_approx"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_iSup_approx"
#print axioms MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_iSup_approx
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_iSup_approx"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_iSup_Ico"
#check @MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_iSup_Ico
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_iSup_Ico"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_iSup_Ico"
#print axioms MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_iSup_Ico
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_iSup_Ico"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_sSup_Iio"
#check @MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_sSup_Iio
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_sSup_Iio"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_sSup_Iio"
#print axioms MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_sSup_Iio
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_eq_sSup_Iio"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.tendsto_openIntervalBudget_approx"
#check @MethbokeAddon.QuasiFeffermanA.tendsto_openIntervalBudget_approx
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.tendsto_openIntervalBudget_approx"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.tendsto_openIntervalBudget_approx"
#print axioms MethbokeAddon.QuasiFeffermanA.tendsto_openIntervalBudget_approx
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.tendsto_openIntervalBudget_approx"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.tendsto_openIntervalBudget_nhdsLT"
#check @MethbokeAddon.QuasiFeffermanA.tendsto_openIntervalBudget_nhdsLT
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.tendsto_openIntervalBudget_nhdsLT"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.tendsto_openIntervalBudget_nhdsLT"
#print axioms MethbokeAddon.QuasiFeffermanA.tendsto_openIntervalBudget_nhdsLT
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.tendsto_openIntervalBudget_nhdsLT"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ne_top_iff_uniform_bound"
#check @MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ne_top_iff_uniform_bound
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ne_top_iff_uniform_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ne_top_iff_uniform_bound"
#print axioms MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ne_top_iff_uniform_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ne_top_iff_uniform_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ne_top_iff_uniform_approx_bound"
#check @MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ne_top_iff_uniform_approx_bound
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ne_top_iff_uniform_approx_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ne_top_iff_uniform_approx_bound"
#print axioms MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ne_top_iff_uniform_approx_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ne_top_iff_uniform_approx_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_iSup_approx"
#check @MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_iSup_approx
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_iSup_approx"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_iSup_approx"
#print axioms MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_iSup_approx
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_iSup_approx"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_iSup_Ico"
#check @MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_iSup_Ico
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_iSup_Ico"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_iSup_Ico"
#print axioms MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_iSup_Ico
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_eq_iSup_Ico"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.tendsto_fullStoppedBudget_approx"
#check @MethbokeAddon.QuasiFeffermanA.tendsto_fullStoppedBudget_approx
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.tendsto_fullStoppedBudget_approx"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.tendsto_fullStoppedBudget_approx"
#print axioms MethbokeAddon.QuasiFeffermanA.tendsto_fullStoppedBudget_approx
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.tendsto_fullStoppedBudget_approx"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.tendsto_fullStoppedBudget_nhdsLT"
#check @MethbokeAddon.QuasiFeffermanA.tendsto_fullStoppedBudget_nhdsLT
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.tendsto_fullStoppedBudget_nhdsLT"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.tendsto_fullStoppedBudget_nhdsLT"
#print axioms MethbokeAddon.QuasiFeffermanA.tendsto_fullStoppedBudget_nhdsLT
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.tendsto_fullStoppedBudget_nhdsLT"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_ne_top_iff_uniform_bound"
#check @MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_ne_top_iff_uniform_bound
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_ne_top_iff_uniform_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_ne_top_iff_uniform_bound"
#print axioms MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_ne_top_iff_uniform_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_ne_top_iff_uniform_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_ne_top_iff_uniform_approx_bound"
#check @MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_ne_top_iff_uniform_approx_bound
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_ne_top_iff_uniform_approx_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_ne_top_iff_uniform_approx_bound"
#print axioms MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_ne_top_iff_uniform_approx_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fullStoppedBudget_ne_top_iff_uniform_approx_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ofReal_eq_integral"
#check @MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ofReal_eq_integral
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ofReal_eq_integral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ofReal_eq_integral"
#print axioms MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ofReal_eq_integral
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_ofReal_eq_integral"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_eq_integral"
#check @MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_eq_integral
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_eq_integral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_eq_integral"
#print axioms MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_eq_integral
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_eq_integral"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_ne_top"
#check @MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_ne_top
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_ne_top"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_ne_top"
#print axioms MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_ne_top
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_ne_top"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_eq_intervalIntegral"
#check @MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_eq_intervalIntegral
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_eq_intervalIntegral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_eq_intervalIntegral"
#print axioms MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_eq_intervalIntegral
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.openIntervalBudget_sq_eq_intervalIntegral"

