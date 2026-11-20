import MethbokeAddon.FDSNR3.Contracts
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual active and untouched continuous-frequency regions

Given 0 < r < ‖c‖, the active ball is centered at c. The anchor is centered
at c + (r/2)e₀. Both have radius r/16 and disjoint compact closures inside
the supplied ball c r. An explicit smooth bump with radii r/8,r/4 is made
odd by subtracting its reflection. Its frequency support is compact and
stays away from zero.
-/

set_option autoImplicit false

open Set Metric SingularClosure
open scoped ContDiff Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

def frequencyBump (c : Vec) (r : ℝ) (hr : 0 < r) : ContDiffBump c where
  rIn := r / 8
  rOut := r / 4
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def frequencyAnchor (c : Vec) (r : ℝ) : Vec :=
  c + (r / 2) • unitVector (0 : Fin 3)

def oddFrequencyCutoff (c : Vec) (r : ℝ) (hr : 0 < r) (ξ : Vec) : ℝ :=
  frequencyBump c r hr ξ - frequencyBump c r hr (-ξ)

theorem dist_frequencyAnchor (c : Vec) {r : ℝ} (hr : 0 ≤ r) :
    dist (frequencyAnchor c r) c = r / 2 := by
  simp [frequencyAnchor, dist_eq_norm, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hr (by norm_num)), unitVector]

theorem dist_self_neg_frequency (c : Vec) :
    dist c (-c) = 2 * ‖c‖ := by
  rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ c, norm_smul]
  norm_num

theorem reflected_frequency_dist (c ξ : Vec) :
    dist (-ξ) c = dist ξ (-c) := by
  simpa only [neg_neg] using (dist_neg_neg ξ (-c))

theorem active_closedBall_subset {c : Vec} {r : ℝ} (hr : 0 < r) :
    closedBall c (r / 16) ⊆ ball c r := by
  intro ξ hξ
  change dist ξ c ≤ r / 16 at hξ
  change dist ξ c < r
  linarith

theorem anchor_closedBall_subset {c : Vec} {r : ℝ} (hr : 0 < r) :
    closedBall (frequencyAnchor c r) (r / 16) ⊆ ball c r := by
  intro ξ hξ
  change dist ξ (frequencyAnchor c r) ≤ r / 16 at hξ
  have htri := dist_triangle ξ (frequencyAnchor c r) c
  rw [dist_frequencyAnchor c hr.le] at htri
  change dist ξ c < r
  linarith

theorem active_anchor_closedBall_disjoint {c : Vec} {r : ℝ} (hr : 0 < r) :
    Disjoint (closedBall c (r / 16))
      (closedBall (frequencyAnchor c r) (r / 16)) := by
  apply Set.disjoint_left.mpr
  intro ξ hc hb
  change dist ξ c ≤ r / 16 at hc
  change dist ξ (frequencyAnchor c r) ≤ r / 16 at hb
  have htri := dist_triangle (frequencyAnchor c r) ξ c
  rw [dist_frequencyAnchor c hr.le, dist_comm (frequencyAnchor c r) ξ] at htri
  linarith

theorem frequencyBump_reflected_eq_zero
    {c : Vec} {r : ℝ} (hr : 0 < r) (haway : r < ‖c‖)
    {ξ : Vec} (hξ : ξ ∈ ball c r) :
    frequencyBump c r hr (-ξ) = 0 := by
  apply (frequencyBump c r hr).zero_of_le_dist
  change r / 4 ≤ dist (-ξ) c
  have htri := dist_triangle c ξ (-c)
  rw [dist_self_neg_frequency, dist_comm c ξ, ← reflected_frequency_dist] at htri
  change dist ξ c < r at hξ
  linarith

theorem oddFrequencyCutoff_contDiff (c : Vec) (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ ∞ (oddFrequencyCutoff c r hr) :=
  (frequencyBump c r hr).contDiff.sub
    ((frequencyBump c r hr).contDiff.comp contDiff_neg)

theorem oddFrequencyCutoff_odd (c : Vec) (r : ℝ) (hr : 0 < r) (ξ : Vec) :
    oddFrequencyCutoff c r hr (-ξ) = -oddFrequencyCutoff c r hr ξ := by
  simp only [oddFrequencyCutoff, neg_neg]
  ring

theorem oddFrequencyCutoff_abs_le_one (c : Vec) (r : ℝ) (hr : 0 < r) (ξ : Vec) :
    |oddFrequencyCutoff c r hr ξ| ≤ 1 := by
  have hp0 : 0 ≤ frequencyBump c r hr ξ := (frequencyBump c r hr).nonneg
  have hp1 : frequencyBump c r hr ξ ≤ 1 := (frequencyBump c r hr).le_one
  have hn0 : 0 ≤ frequencyBump c r hr (-ξ) := (frequencyBump c r hr).nonneg
  have hn1 : frequencyBump c r hr (-ξ) ≤ 1 := (frequencyBump c r hr).le_one
  unfold oddFrequencyCutoff
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem oddFrequencyCutoff_eq_one_on_active
    {c : Vec} {r : ℝ} (hr : 0 < r) (haway : r < ‖c‖)
    {ξ : Vec} (hξ : ξ ∈ closedBall c (r / 16)) :
    oddFrequencyCutoff c r hr ξ = 1 := by
  have hp : frequencyBump c r hr ξ = 1 := by
    apply (frequencyBump c r hr).one_of_mem_closedBall
    change dist ξ c ≤ r / 8
    change dist ξ c ≤ r / 16 at hξ
    linarith
  rw [oddFrequencyCutoff, hp, frequencyBump_reflected_eq_zero hr haway
    (active_closedBall_subset hr hξ), sub_zero]

theorem oddFrequencyCutoff_eq_zero_on_anchor
    {c : Vec} {r : ℝ} (hr : 0 < r) (haway : r < ‖c‖)
    {ξ : Vec} (hξ : ξ ∈ closedBall (frequencyAnchor c r) (r / 16)) :
    oddFrequencyCutoff c r hr ξ = 0 := by
  have hp : frequencyBump c r hr ξ = 0 := by
    apply (frequencyBump c r hr).zero_of_le_dist
    change r / 4 ≤ dist ξ c
    have htri := dist_triangle (frequencyAnchor c r) ξ c
    rw [dist_frequencyAnchor c hr.le, dist_comm (frequencyAnchor c r) ξ] at htri
    change dist ξ (frequencyAnchor c r) ≤ r / 16 at hξ
    linarith
  rw [oddFrequencyCutoff, hp, frequencyBump_reflected_eq_zero hr haway
    (anchor_closedBall_subset hr hξ), sub_self]

theorem oddFrequencyCutoff_eq_zero_of_small_norm
    {c : Vec} {r : ℝ} (hr : 0 < r) (haway : r < ‖c‖)
    {ξ : Vec} (hξ : ‖ξ‖ < ‖c‖ / 2) :
    oddFrequencyCutoff c r hr ξ = 0 := by
  have hp : frequencyBump c r hr ξ = 0 := by
    apply (frequencyBump c r hr).zero_of_le_dist
    change r / 4 ≤ dist ξ c
    have htri := dist_triangle c ξ 0
    rw [dist_zero_right, dist_zero_right, dist_comm c ξ] at htri
    linarith
  have hn : frequencyBump c r hr (-ξ) = 0 := by
    apply (frequencyBump c r hr).zero_of_le_dist
    change r / 4 ≤ dist (-ξ) c
    have htri := dist_triangle c (-ξ) 0
    rw [dist_zero_right, dist_zero_right, norm_neg, dist_comm c (-ξ)] at htri
    linarith
  simp only [oddFrequencyCutoff, hp, hn, sub_self]

theorem oddFrequencyCutoff_tsupport_subset (c : Vec) (r : ℝ) (hr : 0 < r) :
    tsupport (oddFrequencyCutoff c r hr) ⊆
      closedBall c (r / 4) ∪ closedBall (-c) (r / 4) := by
  apply closure_minimal ?_ (isClosed_closedBall.union isClosed_closedBall)
  intro ξ hξ
  by_contra hcarrier
  have hp : frequencyBump c r hr ξ = 0 := by
    apply (frequencyBump c r hr).zero_of_le_dist
    change r / 4 ≤ dist ξ c
    have hnot : ξ ∉ closedBall c (r / 4) := fun h => hcarrier (Or.inl h)
    have hdist : ¬ dist ξ c ≤ r / 4 := hnot
    exact (lt_of_not_ge hdist).le
  have hn : frequencyBump c r hr (-ξ) = 0 := by
    apply (frequencyBump c r hr).zero_of_le_dist
    change r / 4 ≤ dist (-ξ) c
    rw [reflected_frequency_dist]
    have hnot : ξ ∉ closedBall (-c) (r / 4) := fun h => hcarrier (Or.inr h)
    have hdist : ¬ dist ξ (-c) ≤ r / 4 := hnot
    exact (lt_of_not_ge hdist).le
  exact hξ (by simp only [oddFrequencyCutoff, hp, hn, sub_self])

theorem oddFrequencyCutoff_hasCompactSupport (c : Vec) (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (oddFrequencyCutoff c r hr) := by
  exact ((isCompact_closedBall c (r / 4)).union
    (isCompact_closedBall (-c) (r / 4))).of_isClosed_subset
      isClosed_closure (oddFrequencyCutoff_tsupport_subset c r hr)

theorem oddFrequencyCutoff_zero_notMem_tsupport
    {c : Vec} {r : ℝ} (hr : 0 < r) (haway : r < ‖c‖) :
    (0 : Vec) ∉ tsupport (oddFrequencyCutoff c r hr) := by
  intro h
  rcases oddFrequencyCutoff_tsupport_subset c r hr h with hp | hn
  · have hdist : ‖c‖ ≤ r / 4 := by
      simpa only [Metric.mem_closedBall, dist_zero_left] using hp
    linarith
  · have hdist : ‖c‖ ≤ r / 4 := by
      simpa only [Metric.mem_closedBall, dist_zero_left, norm_neg] using hn
    linarith

/-- Actual construction of two nonempty open patches with disjoint compact
closures, and one smooth compactly supported odd frequency phase. -/
theorem exists_odd_frequency_cutoff
    {c : Vec} {r : ℝ} (hr : 0 < r) (haway : r < ‖c‖) :
    ∃ ψ : Vec → ℝ, ∃ b : Vec, ∃ δ ρ : ℝ,
      0 < δ ∧ 0 < ρ ∧
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ ξ : Vec, ψ (-ξ) = -ψ ξ) ∧
      (∀ ξ : Vec, |ψ ξ| ≤ 1) ∧
      closedBall c δ ⊆ ball c r ∧
      closedBall b δ ⊆ ball c r ∧
      Disjoint (closedBall c δ) (closedBall b δ) ∧
      (∀ ξ ∈ closedBall c δ, ψ ξ = 1) ∧
      (∀ ξ ∈ closedBall b δ, ψ ξ = 0) ∧
      (∀ ξ : Vec, ‖ξ‖ < ρ → ψ ξ = 0) ∧
      (0 : Vec) ∉ tsupport ψ := by
  refine ⟨oddFrequencyCutoff c r hr, frequencyAnchor c r, r / 16, ‖c‖ / 2,
    by positivity, by linarith, oddFrequencyCutoff_contDiff c r hr,
    oddFrequencyCutoff_hasCompactSupport c r hr,
    oddFrequencyCutoff_odd c r hr, oddFrequencyCutoff_abs_le_one c r hr,
    active_closedBall_subset hr, anchor_closedBall_subset hr,
    active_anchor_closedBall_disjoint hr, ?_, ?_, ?_,
    oddFrequencyCutoff_zero_notMem_tsupport hr haway⟩
  · exact fun ξ hξ => oddFrequencyCutoff_eq_one_on_active hr haway hξ
  · exact fun ξ hξ => oddFrequencyCutoff_eq_zero_on_anchor hr haway hξ
  · exact fun ξ hξ => oddFrequencyCutoff_eq_zero_of_small_norm hr haway hξ

end

end MethbokeAddon.FDSNR3

