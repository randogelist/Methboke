import MethbokeAddon.FDSN.TimeBump
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Separation.Basic

/-!
# A common nonvanishing time slab

This realizes the local continuity step of FDSN K06. The supplied scalar
function may be the already-identified nonzero helical triad correlation.
-/

noncomputable section

open Set
open scoped ContDiff Topology

namespace MethbokeAddon.FDSN

/-- Local nonvanishing can be maintained on a closed time slab lying strictly
inside any given interval around the distinguished time. -/
theorem exists_nonvanishing_closed_slab {s t T : ℝ} {g : ℝ → ℂ}
    (hst : s < t) (htT : t < T)
    (hg : ContinuousAt g t) (hgt : g t ≠ 0) :
    ∃ a b : ℝ,
      s < a ∧ a < t ∧ t < b ∧ b < T ∧
      ∀ u : ℝ, u ∈ Icc a b → g u ≠ 0 := by
  obtain ⟨ρ, hρ, hρne⟩ := Metric.eventually_nhds_iff.mp (hg.eventually_ne hgt)
  let δ : ℝ := min ρ (min (t - s) (T - t))
  have hδ : 0 < δ := lt_min hρ (lt_min (sub_pos.mpr hst) (sub_pos.mpr htT))
  have hδρ : δ ≤ ρ := min_le_left _ _
  have hδleft : δ ≤ t - s :=
    (min_le_right ρ (min (t - s) (T - t))).trans (min_le_left _ _)
  have hδright : δ ≤ T - t :=
    (min_le_right ρ (min (t - s) (T - t))).trans (min_le_right _ _)
  refine ⟨t - δ / 2, t + δ / 2, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · intro u hu
    obtain ⟨hlo, hhi⟩ := hu
    apply hρne
    rw [Real.dist_eq]
    have habs : |u - t| ≤ δ / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    exact habs.trans_lt (by linarith)

/-- A normalized bump can be chosen so the supplied continuous scalar
correlation stays nonzero throughout its closed support. -/
theorem exists_normalized_bump_on_nonvanishing_slab
    {s t T : ℝ} {g : ℝ → ℂ}
    (hst : s < t) (htT : t < T)
    (hg : ContinuousAt g t) (hgt : g t ≠ 0) :
    ∃ β : ℝ → ℝ,
      ContDiff ℝ ∞ β ∧
      HasCompactSupport β ∧
      tsupport β ⊆ Ioo s T ∧
      β t = 1 ∧
      (∀ u : ℝ, 0 ≤ β u ∧ β u ≤ 1) ∧
      ∀ u : ℝ, u ∈ tsupport β → g u ≠ 0 := by
  obtain ⟨a, b, hsa, hat, htb, hbT, habg⟩ :=
    exists_nonvanishing_closed_slab hst htT hg hgt
  obtain ⟨β, hβsmooth, hβcompact, hβsupport, hβt, hβbounds⟩ :=
    exists_normalized_time_bump hat htb
  refine ⟨β, hβsmooth, hβcompact, ?_, hβt, hβbounds, ?_⟩
  · intro u hu
    obtain ⟨hau, hub⟩ := hβsupport hu
    exact ⟨hsa.trans hau, hub.trans hbT⟩
  · intro u hu
    obtain ⟨hau, hub⟩ := hβsupport hu
    exact habg u ⟨hau.le, hub.le⟩

end MethbokeAddon.FDSN

