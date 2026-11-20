import MethbokeAddon.QuasiFeffermanA.StoppedWindow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Complete stopped nonnegative budgets

Full endpoint budgets remain in `ENNReal`. Increasing partial intervals
recover the entire budget, including an infinite value. Finiteness is
equivalent to one common finite bound for every partial budget, not to
finiteness of each partial budget separately. No temporal measurability
is needed for the directed-union identity. Ordinary-integral bridges
retain the explicit integrability or compact-continuity premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace MethbokeAddon.QuasiFeffermanA

/-- The complete nonnegative budget on a real open interval. -/
def openIntervalBudget (f : ℝ → ℝ≥0∞) (b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) b, f t

/-- The same density observed only before the extended lifetime and finite cutoff. -/
def fullStoppedBudget (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in stoppedObservation T τ, f t

theorem fullStoppedBudget_eq_openIntervalBudget
    (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    fullStoppedBudget f T τ = openIntervalBudget f (stoppedEndpoint T τ) := by
  simp only [fullStoppedBudget, openIntervalBudget, stoppedObservation_eq_Ioo]

@[simp] theorem openIntervalBudget_zero_window (f : ℝ → ℝ≥0∞) :
    openIntervalBudget f 0 = 0 := by
  simp [openIntervalBudget]

@[simp] theorem openIntervalBudget_zero (b : ℝ) :
    openIntervalBudget (fun _ : ℝ => 0) b = 0 := by
  simp [openIntervalBudget]

theorem openIntervalBudget_mono (f : ℝ → ℝ≥0∞) :
    Monotone (openIntervalBudget f) := by
  intro a b hab
  exact lintegral_mono_set (Ioo_subset_Ioo_right hab)

theorem openIntervalBudget_mono_integrand {f g : ℝ → ℝ≥0∞}
    (b : ℝ) (h : ∀ t, f t ≤ g t) :
    openIntervalBudget f b ≤ openIntervalBudget g b :=
  lintegral_mono h

theorem openIntervalBudget_congr {f g : ℝ → ℝ≥0∞} (b : ℝ)
    (h : ∀ t ∈ Ioo (0 : ℝ) b, f t = g t) :
    openIntervalBudget f b = openIntervalBudget g b :=
  setLIntegral_congr_fun measurableSet_Ioo h

@[simp] theorem fullStoppedBudget_zero (T : ℝ≥0∞) (τ : ℝ) :
    fullStoppedBudget (fun _ : ℝ => 0) T τ = 0 := by
  simp [fullStoppedBudget]

@[simp] theorem fullStoppedBudget_zero_lifetime (f : ℝ → ℝ≥0∞) (τ : ℝ) :
    fullStoppedBudget f 0 τ = 0 := by
  simp [fullStoppedBudget]

@[simp] theorem fullStoppedBudget_zero_cutoff (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) :
    fullStoppedBudget f T 0 = 0 := by
  simp [fullStoppedBudget]

theorem fullStoppedBudget_top (f : ℝ → ℝ≥0∞) {τ : ℝ} (hτ : 0 ≤ τ) :
    fullStoppedBudget f (∞ : ℝ≥0∞) τ = openIntervalBudget f τ := by
  rw [fullStoppedBudget_eq_openIntervalBudget, stoppedEndpoint_top hτ]

theorem fullStoppedBudget_mono {f g : ℝ → ℝ≥0∞}
    (T : ℝ≥0∞) (τ : ℝ) (h : ∀ t, f t ≤ g t) :
    fullStoppedBudget f T τ ≤ fullStoppedBudget g T τ :=
  lintegral_mono h

theorem fullStoppedBudget_mono_window (f : ℝ → ℝ≥0∞)
    {T₁ T₂ : ℝ≥0∞} {τ₁ τ₂ : ℝ} (hT : T₁ ≤ T₂) (hτ : τ₁ ≤ τ₂) :
    fullStoppedBudget f T₁ τ₁ ≤ fullStoppedBudget f T₂ τ₂ :=
  lintegral_mono_set (stoppedObservation_mono hT hτ)

/-- Values outside the actual observation set have no effect on the budget. -/
theorem fullStoppedBudget_congr {f g : ℝ → ℝ≥0∞}
    (T : ℝ≥0∞) (τ : ℝ)
    (h : ∀ t ∈ stoppedObservation T τ, f t = g t) :
    fullStoppedBudget f T τ = fullStoppedBudget g T τ :=
  setLIntegral_congr_fun (measurableSet_stoppedObservation T τ) h

theorem fullStoppedBudget_congr_ae {f g : ℝ → ℝ≥0∞}
    (T : ℝ≥0∞) (τ : ℝ)
    (h : f =ᵐ[volume.restrict (stoppedObservation T τ)] g) :
    fullStoppedBudget f T τ = fullStoppedBudget g T τ :=
  lintegral_congr_ae h

/-- Finite constant extraction does not require measurability or a finite budget. -/
theorem fullStoppedBudget_const_mul
    (c : ℝ≥0∞) (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ)
    (hc : c ≠ (∞ : ℝ≥0∞)) :
    fullStoppedBudget (fun t => c * f t) T τ = c * fullStoppedBudget f T τ :=
  lintegral_const_mul' c f hc

/-- An explicit cofinal increasing family of strict subendpoints. -/
def budgetApproxEndpoint (b : ℝ) (n : ℕ) : ℝ :=
  b * ((n : ℝ) + 1) / ((n : ℝ) + 2)

theorem budgetApproxEndpoint_eq_sub (b : ℝ) (n : ℕ) :
    budgetApproxEndpoint b n = b - b / ((n : ℝ) + 2) := by
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  unfold budgetApproxEndpoint
  field_simp [hn]
  <;> ring

@[simp] theorem budgetApproxEndpoint_zero (n : ℕ) :
    budgetApproxEndpoint 0 n = 0 := by
  simp [budgetApproxEndpoint]

theorem budgetApproxEndpoint_nonneg {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    0 ≤ budgetApproxEndpoint b n := by
  unfold budgetApproxEndpoint
  positivity

theorem budgetApproxEndpoint_le {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    budgetApproxEndpoint b n ≤ b := by
  rw [budgetApproxEndpoint_eq_sub]
  exact sub_le_self _ (div_nonneg hb (by positivity))

theorem budgetApproxEndpoint_lt {b : ℝ} (hb : 0 < b) (n : ℕ) :
    budgetApproxEndpoint b n < b := by
  rw [budgetApproxEndpoint_eq_sub]
  exact sub_lt_self _ (div_pos hb (by positivity))

theorem budgetApproxEndpoint_mono {b : ℝ} (hb : 0 ≤ b) :
    Monotone (budgetApproxEndpoint b) := by
  intro n m hnm
  rw [budgetApproxEndpoint_eq_sub, budgetApproxEndpoint_eq_sub]
  apply sub_le_sub_left
  apply div_le_div_of_nonneg_left hb (by positivity)
  exact_mod_cast Nat.add_le_add_right hnm 2

theorem tendsto_budgetApproxEndpoint (b : ℝ) :
    Tendsto (budgetApproxEndpoint b) atTop (𝓝 b) := by
  have hshift : Tendsto (fun n : ℕ => b / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 2).2 (tendsto_const_div_atTop_nhds_zero_nat b)
  have hdiv : Tendsto (fun n : ℕ => b / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hshift
  have heq : budgetApproxEndpoint b = fun n : ℕ => b - b / ((n : ℝ) + 2) := by
    funext n
    exact budgetApproxEndpoint_eq_sub b n
  rw [heq]
  simpa only [sub_zero] using
    (tendsto_const_nhds (x := b)).sub hdiv

theorem budgetApproxEndpoint_cofinal (b : ℝ) {r : ℝ} (hr : r < b) :
    ∃ n : ℕ, r < budgetApproxEndpoint b n := by
  have h : ∀ᶠ n : ℕ in atTop, r < budgetApproxEndpoint b n :=
    (tendsto_order.mp (tendsto_budgetApproxEndpoint b)).1 r hr
  exact h.exists

theorem iUnion_Ioo_budgetApproxEndpoint {b : ℝ} (hb : 0 ≤ b) :
    (⋃ n : ℕ, Ioo (0 : ℝ) (budgetApproxEndpoint b n)) = Ioo (0 : ℝ) b := by
  ext t
  constructor
  · intro ht
    rcases mem_iUnion.mp ht with ⟨n, hn⟩
    exact ⟨hn.1, hn.2.trans_le (budgetApproxEndpoint_le hb n)⟩
  · intro ht
    rcases budgetApproxEndpoint_cofinal b ht.2 with ⟨n, hn⟩
    exact mem_iUnion.mpr ⟨n, ht.1, hn⟩

/-- Countable directed-union continuity preserves infinite endpoint budgets. -/
theorem openIntervalBudget_eq_iSup_approx (f : ℝ → ℝ≥0∞) {b : ℝ} (hb : 0 ≤ b) :
    openIntervalBudget f b = ⨆ n : ℕ, openIntervalBudget f (budgetApproxEndpoint b n) := by
  change (∫⁻ t in Ioo (0 : ℝ) b, f t) =
    ⨆ n : ℕ, ∫⁻ t in Ioo (0 : ℝ) (budgetApproxEndpoint b n), f t
  rw [← iUnion_Ioo_budgetApproxEndpoint hb]
  apply setLIntegral_iUnion_of_directed
  intro n m
  refine ⟨max n m, ?_, ?_⟩
  · exact Ioo_subset_Ioo_right (budgetApproxEndpoint_mono hb (le_max_left _ _))
  · exact Ioo_subset_Ioo_right (budgetApproxEndpoint_mono hb (le_max_right _ _))

/-- The full budget is the supremum over every nonnegative strict subendpoint. -/
theorem openIntervalBudget_eq_iSup_Ico (f : ℝ → ℝ≥0∞) {b : ℝ} (hb : 0 ≤ b) :
    openIntervalBudget f b = ⨆ r ∈ Ico (0 : ℝ) b, openIntervalBudget f r := by
  apply le_antisymm
  · rcases eq_or_lt_of_le hb with hb0 | hbpos
    · subst b
      rw [openIntervalBudget_zero_window]
      exact bot_le
    · rw [openIntervalBudget_eq_iSup_approx f hb]
      apply iSup_le
      intro n
      exact le_iSup_of_le (budgetApproxEndpoint b n)
        (le_iSup_of_le ⟨budgetApproxEndpoint_nonneg hb n,
          budgetApproxEndpoint_lt hbpos n⟩ le_rfl)
  · refine iSup_le fun r => iSup_le fun hr => ?_
    exact openIntervalBudget_mono f hr.2.le

/-- The supremum of all values below `b` is the same complete budget. -/
theorem openIntervalBudget_eq_sSup_Iio (f : ℝ → ℝ≥0∞) {b : ℝ} (hb : 0 ≤ b) :
    openIntervalBudget f b = sSup (openIntervalBudget f '' Iio b) := by
  apply le_antisymm
  · rcases eq_or_lt_of_le hb with hb0 | hbpos
    · subst b
      rw [openIntervalBudget_zero_window]
      exact bot_le
    · rw [openIntervalBudget_eq_iSup_approx f hb]
      apply iSup_le
      intro n
      exact le_sSup ⟨budgetApproxEndpoint b n, budgetApproxEndpoint_lt hbpos n, rfl⟩
  · apply sSup_le
    rintro _ ⟨r, hr, rfl⟩
    exact openIntervalBudget_mono f hr.le

/-- Literal monotone partial-budget convergence in `ENNReal`, including infinity. -/
theorem tendsto_openIntervalBudget_approx (f : ℝ → ℝ≥0∞) {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ => openIntervalBudget f (budgetApproxEndpoint b n))
      atTop (𝓝 (openIntervalBudget f b)) := by
  have hmono : Monotone (fun n : ℕ => openIntervalBudget f (budgetApproxEndpoint b n)) :=
    (openIntervalBudget_mono f).comp (budgetApproxEndpoint_mono hb)
  have h := tendsto_atTop_iSup hmono
  rwa [← openIntervalBudget_eq_iSup_approx f hb] at h

/-- The complete improper limit from below, not merely a selected sequence. -/
theorem tendsto_openIntervalBudget_nhdsLT (f : ℝ → ℝ≥0∞) {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (openIntervalBudget f) (𝓝[<] b) (𝓝 (openIntervalBudget f b)) := by
  have h := (openIntervalBudget_mono f).tendsto_nhdsLT b
  rwa [← openIntervalBudget_eq_sSup_Iio f hb] at h

/-- Finiteness means one common finite bound for all partial budgets. -/
theorem openIntervalBudget_ne_top_iff_uniform_bound
    (f : ℝ → ℝ≥0∞) {b : ℝ} (hb : 0 ≤ b) :
    openIntervalBudget f b ≠ (∞ : ℝ≥0∞) ↔
      ∃ C : ℝ≥0, ∀ r ∈ Ico (0 : ℝ) b, openIntervalBudget f r ≤ (C : ℝ≥0∞) := by
  constructor
  · intro hfinite
    refine ⟨(openIntervalBudget f b).toNNReal, ?_⟩
    intro r hr
    rw [ENNReal.coe_toNNReal hfinite]
    exact openIntervalBudget_mono f hr.2.le
  · rintro ⟨C, hC⟩
    apply ne_top_of_le_ne_top
      (show (C : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) from ENNReal.coe_ne_top)
    rw [openIntervalBudget_eq_iSup_Ico f hb]
    exact iSup_le fun r => iSup_le fun hr => hC r hr

theorem openIntervalBudget_ne_top_iff_uniform_approx_bound
    (f : ℝ → ℝ≥0∞) {b : ℝ} (hb : 0 ≤ b) :
    openIntervalBudget f b ≠ (∞ : ℝ≥0∞) ↔
      ∃ C : ℝ≥0, ∀ n : ℕ,
        openIntervalBudget f (budgetApproxEndpoint b n) ≤ (C : ℝ≥0∞) := by
  constructor
  · intro hfinite
    refine ⟨(openIntervalBudget f b).toNNReal, ?_⟩
    intro n
    rw [ENNReal.coe_toNNReal hfinite]
    exact openIntervalBudget_mono f (budgetApproxEndpoint_le hb n)
  · rintro ⟨C, hC⟩
    apply ne_top_of_le_ne_top
      (show (C : ℝ≥0∞) ≠ (∞ : ℝ≥0∞) from ENNReal.coe_ne_top)
    rw [openIntervalBudget_eq_iSup_approx f hb]
    exact iSup_le hC

theorem fullStoppedBudget_eq_iSup_approx
    (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    fullStoppedBudget f T τ =
      ⨆ n : ℕ, openIntervalBudget f (budgetApproxEndpoint (stoppedEndpoint T τ) n) := by
  rw [fullStoppedBudget_eq_openIntervalBudget]
  exact openIntervalBudget_eq_iSup_approx f (stoppedEndpoint_nonneg T τ)

theorem fullStoppedBudget_eq_iSup_Ico
    (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    fullStoppedBudget f T τ =
      ⨆ r ∈ Ico (0 : ℝ) (stoppedEndpoint T τ), openIntervalBudget f r := by
  rw [fullStoppedBudget_eq_openIntervalBudget]
  exact openIntervalBudget_eq_iSup_Ico f (stoppedEndpoint_nonneg T τ)

theorem tendsto_fullStoppedBudget_approx
    (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    Tendsto (fun n : ℕ => openIntervalBudget f
      (budgetApproxEndpoint (stoppedEndpoint T τ) n)) atTop (𝓝 (fullStoppedBudget f T τ)) := by
  rw [fullStoppedBudget_eq_openIntervalBudget]
  exact tendsto_openIntervalBudget_approx f (stoppedEndpoint_nonneg T τ)

theorem tendsto_fullStoppedBudget_nhdsLT
    (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    Tendsto (openIntervalBudget f) (𝓝[<] stoppedEndpoint T τ)
      (𝓝 (fullStoppedBudget f T τ)) := by
  rw [fullStoppedBudget_eq_openIntervalBudget]
  exact tendsto_openIntervalBudget_nhdsLT f (stoppedEndpoint_nonneg T τ)

theorem fullStoppedBudget_ne_top_iff_uniform_bound
    (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    fullStoppedBudget f T τ ≠ (∞ : ℝ≥0∞) ↔
      ∃ C : ℝ≥0, ∀ r ∈ Ico (0 : ℝ) (stoppedEndpoint T τ),
        openIntervalBudget f r ≤ (C : ℝ≥0∞) := by
  rw [fullStoppedBudget_eq_openIntervalBudget]
  exact openIntervalBudget_ne_top_iff_uniform_bound f (stoppedEndpoint_nonneg T τ)

theorem fullStoppedBudget_ne_top_iff_uniform_approx_bound
    (f : ℝ → ℝ≥0∞) (T : ℝ≥0∞) (τ : ℝ) :
    fullStoppedBudget f T τ ≠ (∞ : ℝ≥0∞) ↔
      ∃ C : ℝ≥0, ∀ n : ℕ, openIntervalBudget f
        (budgetApproxEndpoint (stoppedEndpoint T τ) n) ≤ (C : ℝ≥0∞) := by
  rw [fullStoppedBudget_eq_openIntervalBudget]
  exact openIntervalBudget_ne_top_iff_uniform_approx_bound f (stoppedEndpoint_nonneg T τ)

/-- Ordinary integrals are used only with genuine integrability and nonnegativity. -/
theorem openIntervalBudget_ofReal_eq_integral
    (g : ℝ → ℝ) (b : ℝ)
    (hg : IntegrableOn g (Ioo (0 : ℝ) b) volume)
    (hgnonneg : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) b), 0 ≤ g t) :
    openIntervalBudget (fun t => ENNReal.ofReal (g t)) b =
      ENNReal.ofReal (∫ t in Ioo (0 : ℝ) b, g t) :=
  (ofReal_integral_eq_lintegral_ofReal hg hgnonneg).symm

/-- Compact continuity suffices at a partial endpoint; terminal continuity is not inferred. -/
theorem openIntervalBudget_sq_eq_integral (Y : ℝ → ℝ) {r : ℝ}
    (hY : ContinuousOn Y (Icc (0 : ℝ) r)) :
    openIntervalBudget (fun t => ENNReal.ofReal ((Y t) ^ 2)) r =
      ENNReal.ofReal (∫ t in Ioo (0 : ℝ) r, (Y t) ^ 2) := by
  apply openIntervalBudget_ofReal_eq_integral
  · exact (hY.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  · exact Eventually.of_forall (fun t => sq_nonneg (Y t))

theorem openIntervalBudget_sq_ne_top (Y : ℝ → ℝ) {r : ℝ}
    (hY : ContinuousOn Y (Icc (0 : ℝ) r)) :
    openIntervalBudget (fun t => ENNReal.ofReal ((Y t) ^ 2)) r ≠ (∞ : ℝ≥0∞) := by
  rw [openIntervalBudget_sq_eq_integral Y hY]
  exact ENNReal.ofReal_ne_top

theorem openIntervalBudget_sq_eq_intervalIntegral
    (Y : ℝ → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hY : ContinuousOn Y (Icc (0 : ℝ) r)) :
    openIntervalBudget (fun t => ENNReal.ofReal ((Y t) ^ 2)) r =
      ENNReal.ofReal (∫ t in (0 : ℝ)..r, (Y t) ^ 2) := by
  rw [openIntervalBudget_sq_eq_integral Y hY, intervalIntegral.integral_of_le hr,
    restrict_Ioo_eq_restrict_Ioc]

end MethbokeAddon.QuasiFeffermanA
