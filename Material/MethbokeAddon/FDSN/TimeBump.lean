import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A normalized smooth time bump for the torus FDSN construction

This module is a source candidate prepared without executing Lean locally.
Its first external CI build and named axiom audit determine acceptance.

The radius choice is explicit. In particular, the support sits strictly inside
the prescribed preterminal interval, which supplies collars at both endpoints.
-/

noncomputable section

open Set
open scoped ContDiff Topology

namespace MethbokeAddon.FDSN

/-- A normalized smooth time bump supported compactly inside any open interval
containing the distinguished time. This is the FDSN K07 construction endpoint. -/
theorem exists_normalized_time_bump {s t T : ℝ}
    (hst : s < t) (htT : t < T) :
    ∃ β : ℝ → ℝ,
      ContDiff ℝ ∞ β ∧
      HasCompactSupport β ∧
      tsupport β ⊆ Ioo s T ∧
      β t = 1 ∧
      ∀ u : ℝ, 0 ≤ β u ∧ β u ≤ 1 := by
  let δ : ℝ := min (t - s) (T - t)
  have hδ : 0 < δ := lt_min (sub_pos.mpr hst) (sub_pos.mpr htT)
  have hδ_left : δ ≤ t - s := min_le_left _ _
  have hδ_right : δ ≤ T - t := min_le_right _ _
  let f : ContDiffBump t :=
    { rIn := δ / 4
      rOut := δ / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  refine ⟨f, f.contDiff, f.hasCompactSupport, ?_, ?_, ?_⟩
  · intro u hu
    rw [f.tsupport_eq] at hu
    have hdist : |u - t| ≤ δ / 2 := by
      simpa only [Metric.mem_closedBall, Real.dist_eq] using hu
    obtain ⟨hlo, hhi⟩ := abs_le.mp hdist
    constructor <;> linarith
  · apply f.one_of_mem_closedBall
    exact Metric.mem_closedBall_self f.rIn_pos.le
  · intro u
    exact ⟨f.nonneg, f.le_one⟩

end MethbokeAddon.FDSN

