import MethbokeAddon.FDSN.TimePhase
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Compactly localized coefficients with only preterminal smoothness

A seed coefficient is only required to be smooth on the open preterminal slab
containing the bump support. Its arbitrary total-function extension outside
that slab does not affect the smoothness of the correction.
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace MethbokeAddon.FDSN

/-- A globally smooth factor can localize a coefficient which is smooth only
on an open neighborhood of the factor's closed support. -/
theorem contDiff_mul_of_tsupport_subset {f g : ℝ → ℂ} {S : Set ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiffOn ℝ ∞ g S)
    (hS : IsOpen S) (hfs : tsupport f ⊆ S) :
    ContDiff ℝ ∞ (fun t => f t * g t) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t ∈ tsupport f
  · exact hf.contDiffAt.mul (hg.contDiffAt (hS.mem_nhds (hfs ht)))
  · have hz : f =ᶠ[𝓝 t] 0 := notMem_tsupport_iff_eventuallyEq.mp ht
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    exact hz.mono fun u hu => by simp [hu]

/-- Joint smoothness in parameter and time needs smoothness of the seed
coefficient only on the slab containing the bump support. -/
theorem contDiff_timePhaseIncrement_mul_localCoefficient_joint
    {β : ℝ → ℝ} {a : ℝ → ℂ} {s T : ℝ}
    (hβ : ContDiff ℝ ∞ β)
    (ha : ContDiffOn ℝ ∞ a (Ioo s T))
    (hβs : tsupport β ⊆ Ioo s T) :
    ContDiff ℝ ∞
      (fun q : ℝ × ℝ => timePhaseIncrement β q.1 q.2 * a q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : q.2 ∈ tsupport β
  · exact (contDiff_timePhaseIncrement_joint hβ).contDiffAt.mul
      ((ha.contDiffAt (isOpen_Ioo.mem_nhds (hβs hq))).comp q contDiffAt_snd)
  · have hz : β =ᶠ[𝓝 q.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hq
    have hz' : ∀ᶠ r : ℝ × ℝ in 𝓝 q, β r.2 = 0 :=
      (continuousAt_snd : ContinuousAt (fun r : ℝ × ℝ => r.2) q).tendsto.eventually hz
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    exact hz'.mono fun r hr => by simp [timePhaseIncrement, timePhase, hr]

theorem tsupport_timePhaseIncrement_mul_coefficient_subset
    (β : ℝ → ℝ) (a : ℝ → ℂ) (lambda : ℝ) :
    tsupport (fun t => timePhaseIncrement β lambda t * a t) ⊆ tsupport β :=
  tsupport_mul_subset_left.trans (tsupport_timePhaseIncrement_subset β lambda)

theorem hasCompactSupport_timePhaseIncrement_mul_coefficient
    {β : ℝ → ℝ} (hβ : HasCompactSupport β)
    (a : ℝ → ℂ) (lambda : ℝ) :
    HasCompactSupport (fun t => timePhaseIncrement β lambda t * a t) :=
  (hasCompactSupport_timePhaseIncrement hβ lambda).mul_right

/-- Uniform zero-order parameter smallness of an actual localized coefficient.
The constant is extracted from compact support and local continuity of the
coefficient; no global bound beyond the preterminal slab is assumed. -/
theorem localized_coefficient_uniform_linear_bound
    {β : ℝ → ℝ} {a : ℝ → ℂ} {s T : ℝ}
    (hβcompact : HasCompactSupport β)
    (hβbounds : ∀ t : ℝ, 0 ≤ β t ∧ β t ≤ 1)
    (hβs : tsupport β ⊆ Ioo s T)
    (ha : ContinuousOn a (Ioo s T)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ lambda t : ℝ,
        ‖timePhaseIncrement β lambda t * a t‖ ≤ C * ‖lambda‖ := by
  obtain ⟨C, hC⟩ :=
    hβcompact.isCompact.exists_bound_of_continuousOn (ha.mono hβs)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro lambda t
  by_cases ht : t ∈ tsupport β
  · calc
      ‖timePhaseIncrement β lambda t * a t‖ =
          ‖timePhaseIncrement β lambda t‖ * ‖a t‖ := norm_mul _ _
      _ ≤ ‖lambda‖ * ‖a t‖ :=
        mul_le_mul_of_nonneg_right
          (norm_timePhaseIncrement_le_parameter (hβbounds t).1 (hβbounds t).2 lambda)
          (norm_nonneg _)
      _ ≤ ‖lambda‖ * max C 0 :=
        mul_le_mul_of_nonneg_left ((hC t ht).trans (le_max_left _ _)) (norm_nonneg _)
      _ = max C 0 * ‖lambda‖ := mul_comm _ _
  · have hz : timePhaseIncrement β lambda t = 0 := by
      simp [timePhaseIncrement, timePhase_eq_one_of_notMem_tsupport ht lambda]
    rw [hz, zero_mul, norm_zero]
    exact mul_nonneg (le_max_right _ _) (norm_nonneg _)

end MethbokeAddon.FDSN

