import MethbokeAddon.QuasiFeffermanA.Contracts
import QFA.Endpoints.Restart.TimeTranslate
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Support

/-!
# Actual whole-space weak momentum under a nonnegative time translation

Every original compact positive-time solenoidal test is translated by the
literal affine clock. The three original spatial contractions, their genuine
time integrability, and the weak equation are transported. The discarded
initial time segment contributes zero because the translated test and its
derivatives vanish there. No restarted weak equation is an assumption.

Prepared for matching authorized external compilation and exact type/axiom
audits. No local Lean, Lake or kernel execution is authorized.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Interval Topology

namespace MethbokeAddon.QuasiFeffermanA

open QFA.Endpoints.Restart

private def backwardTimeHomeomorph (s : ℝ) :
    (ℝ × Space) ≃ₜ (ℝ × Space) where
  toFun z := (z.1 - s, z.2)
  invFun z := (z.1 + s, z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  continuous_toFun := (continuous_fst.sub continuous_const).prodMk continuous_snd
  continuous_invFun := (continuous_fst.add continuous_const).prodMk continuous_snd

/-- Move an actual momentum test into the original trajectory's time domain. -/
def MomentumTest.restart (φ : MomentumTest) (s : ℝ) (hs : 0 ≤ s) : MomentumTest where
  value z := φ.value (z.1 - s, z.2)
  smooth := φ.smooth.comp
    ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  compact_support := by
    exact φ.compact_support.comp_homeomorph (backwardTimeHomeomorph s)
  positive_support := by
    intro z hz
    have hm : (z.1 - s, z.2) ∈ tsupport φ.value :=
      tsupport_comp_subset_preimage φ.value
        ((continuous_fst.sub continuous_const).prodMk continuous_snd) hz
    have hp := φ.positive_support hm
    change 0 < z.1 - s at hp
    change 0 < z.1
    linarith
  solenoidal t x := φ.solenoidal (t - s) x

theorem MomentumTest.restart_value (φ : MomentumTest) (s : ℝ) (hs : 0 ≤ s)
    (t : ℝ) (x : Space) :
    (φ.restart s hs).value (t, x) = φ.value (t - s, x) := rfl

/-- The affine backward clock has derivative one, including at the support boundary. -/
theorem MomentumTest.restart_time_fderiv (φ : MomentumTest) (s : ℝ)
    (hs : 0 ≤ s) (t : ℝ) (x : Space) :
    fderiv ℝ (fun r : ℝ => (φ.restart s hs).value (r, x)) t =
      fderiv ℝ (fun r : ℝ => φ.value (r, x)) (t - s) := by
  have hd : DifferentiableAt ℝ (fun r : ℝ => φ.value (r, x)) (t - s) :=
    ((φ.smooth.comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by simp)) (t - s)
  have hc := (hd.hasFDerivAt.comp t (hasFDerivAt_sub_const s)).fderiv
  simpa only [MomentumTest.restart, Function.comp_def, ContinuousLinearMap.comp_id] using hc

theorem MomentumTest.restart_spatial_fderiv (φ : MomentumTest) (s : ℝ)
    (hs : 0 ≤ s) (t : ℝ) (x : Space) :
    fderiv ℝ (fun y : Space => (φ.restart s hs).value (t, y)) x =
      fderiv ℝ (fun y : Space => φ.value (t - s, y)) x := rfl

private theorem MomentumTest.time_fderiv_eq_zero_of_nonpos
    (φ : MomentumTest) {t : ℝ} (ht : t ≤ 0) (x : Space) :
    fderiv ℝ (fun r : ℝ => φ.value (r, x)) t = 0 := by
  apply fderiv_of_notMem_tsupport ℝ
  intro hm
  have hmem : (t, x) ∈ tsupport φ.value :=
    tsupport_comp_subset_preimage φ.value
      (continuous_id.prodMk continuous_const) hm
  exact (not_lt_of_ge ht) (φ.positive_support hmem)

private theorem MomentumTest.spatial_fderiv_eq_zero_of_nonpos
    (φ : MomentumTest) {t : ℝ} (ht : t ≤ 0) (x : Space) :
    fderiv ℝ (fun y : Space => φ.value (t, y)) x = 0 := by
  have heq : (fun y : Space => φ.value (t, y)) = 0 := by
    funext y
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    exact (not_lt_of_ge ht) (φ.positive_support hm)
  rw [heq]
  simp

theorem momentumTimeIntegrand_timeTranslate (s : ℝ) (hs : 0 ≤ s)
    (u : Velocity) (φ : MomentumTest) (t : ℝ) (x : Space) :
    momentumTimeIntegrand (timeTranslate s u) φ t x =
      momentumTimeIntegrand u (φ.restart s hs) (t + s) x := by
  simp only [momentumTimeIntegrand, MomentumTest.restart_time_fderiv,
    add_sub_cancel_right, timeTranslate]

theorem momentumConvectionIntegrand_timeTranslate (s : ℝ) (hs : 0 ≤ s)
    (u : Velocity) (φ : MomentumTest) (t : ℝ) (x : Space) :
    momentumConvectionIntegrand (timeTranslate s u) φ t x =
      momentumConvectionIntegrand u (φ.restart s hs) (t + s) x := by
  simp only [momentumConvectionIntegrand, MomentumTest.restart_spatial_fderiv,
    add_sub_cancel_right, timeTranslate]

theorem momentumDissipationIntegrand_timeTranslate (s : ℝ) (hs : 0 ≤ s)
    (G : WeakGradient) (φ : MomentumTest) (t : ℝ) (x : Space) :
    momentumDissipationIntegrand (timeTranslate s G) φ t x =
      momentumDissipationIntegrand G (φ.restart s hs) (t + s) x := by
  simp only [momentumDissipationIntegrand, MomentumTest.restart_spatial_fderiv,
    add_sub_cancel_right, timeTranslate]

private theorem momentumTimeIntegrand_restart_zero (s : ℝ) (hs : 0 ≤ s)
    (u : Velocity) (φ : MomentumTest) {t : ℝ} (ht : t ≤ s) (x : Space) :
    momentumTimeIntegrand u (φ.restart s hs) t x = 0 := by
  simp only [momentumTimeIntegrand, MomentumTest.restart_time_fderiv,
    φ.time_fderiv_eq_zero_of_nonpos (sub_nonpos.mpr ht) x,
    ContinuousLinearMap.zero_apply, inner_zero]

private theorem momentumConvectionIntegrand_restart_zero (s : ℝ) (hs : 0 ≤ s)
    (u : Velocity) (φ : MomentumTest) {t : ℝ} (ht : t ≤ s) (x : Space) :
    momentumConvectionIntegrand u (φ.restart s hs) t x = 0 := by
  simp only [momentumConvectionIntegrand, MomentumTest.restart_spatial_fderiv,
    φ.spatial_fderiv_eq_zero_of_nonpos (sub_nonpos.mpr ht) x,
    ContinuousLinearMap.zero_apply, inner_zero, mul_zero, Finset.sum_const_zero]

private theorem momentumDissipationIntegrand_restart_zero (s : ℝ) (hs : 0 ≤ s)
    (G : WeakGradient) (φ : MomentumTest) {t : ℝ} (ht : t ≤ s) (x : Space) :
    momentumDissipationIntegrand G (φ.restart s hs) t x = 0 := by
  simp only [momentumDissipationIntegrand, MomentumTest.restart_spatial_fderiv,
    φ.spatial_fderiv_eq_zero_of_nonpos (sub_nonpos.mpr ht) x,
    ContinuousLinearMap.zero_apply, inner_zero, Finset.sum_const_zero]

/-- Exact translation of the positive half-line with its restricted Lebesgue measure. -/
theorem timeTranslate_measurePreserving_Ioi (s : ℝ) :
    MeasurePreserving (fun t : ℝ => t + s)
      (volume.restrict (Ioi (0 : ℝ))) (volume.restrict (Ioi s)) := by
  have hmp : MeasurePreserving (fun t : ℝ => t + s) volume volume :=
    ⟨(continuous_id.add continuous_const).measurable, map_add_right_eq_self volume s⟩
  have hpre : (fun t : ℝ => t + s) ⁻¹' Ioi s = Ioi (0 : ℝ) := by
    ext t
    change (s < t + s) ↔ 0 < t
    constructor <;> intro h <;> linarith
  simpa only [hpre] using hmp.restrict_preimage (s := Ioi s) measurableSet_Ioi

/-- Genuine integrability is restricted before pulling back along the clock. -/
theorem timeTranslate_integrable_Ioi {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℝ}
    (hf : Integrable f (volume.restrict (Ioi (0 : ℝ)))) :
    Integrable (fun t : ℝ => f (t + s)) (volume.restrict (Ioi (0 : ℝ))) := by
  have hsub : Ioi s ⊆ Ioi (0 : ℝ) := fun t ht => hs.trans_lt ht
  have hr := hf.mono_measure (Measure.restrict_mono_set volume hsub)
  exact (timeTranslate_measurePreserving_Ioi s).integrable_comp_of_integrable hr

/-- The initial segment disappears only under the explicit vanishing hypothesis. -/
theorem timeTranslate_integral_Ioi_of_zero_before {s : ℝ} (hs : 0 ≤ s)
    (f : ℝ → ℝ) (hzero : ∀ t : ℝ, t ≤ s → f t = 0) :
    (∫ t in Ioi (0 : ℝ), f (t + s)) = ∫ t in Ioi (0 : ℝ), f t := by
  calc
    (∫ t in Ioi (0 : ℝ), f (t + s)) = ∫ t in Ioi s, f t :=
      (timeTranslate_measurePreserving_Ioi s).integral_comp
        (Homeomorph.addRight s).measurableEmbedding f
    _ = ∫ t in Ioi (0 : ℝ), f t := by
      symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (show Ioi s ⊆ Ioi (0 : ℝ) from fun t ht => hs.trans_lt ht)
      intro t ht
      exact hzero t (le_of_not_gt ht.2)

/-- Literal physical weak momentum, including all three integrability clauses,
is preserved by every nonnegative translation. -/
theorem WeakMomentum.timeTranslate {ν s : ℝ} {u : Velocity} {G : WeakGradient}
    (h : WeakMomentum ν u G) (hs : 0 ≤ s) :
    WeakMomentum ν (timeTranslate s u) (timeTranslate s G) := by
  constructor
  · intro φ t ht
    obtain ⟨hT, hC, hD⟩ := h.spatial_integrability (φ.restart s hs)
      (t + s) (add_nonneg ht hs)
    refine ⟨?_, ?_, ?_⟩
    · exact hT.congr (Filter.Eventually.of_forall fun x =>
        (momentumTimeIntegrand_timeTranslate s hs u φ t x).symm)
    · exact hC.congr (Filter.Eventually.of_forall fun x =>
        (momentumConvectionIntegrand_timeTranslate s hs u φ t x).symm)
    · exact hD.congr (Filter.Eventually.of_forall fun x =>
        (momentumDissipationIntegrand_timeTranslate s hs G φ t x).symm)
  · intro φ
    obtain ⟨hT, hC, hD⟩ := h.time_integrability (φ.restart s hs)
    refine ⟨?_, ?_, ?_⟩
    · simpa only [← momentumTimeIntegrand_timeTranslate s hs] using
        (timeTranslate_integrable_Ioi hs hT)
    · simpa only [← momentumConvectionIntegrand_timeTranslate s hs] using
        (timeTranslate_integrable_Ioi hs hC)
    · simpa only [← momentumDissipationIntegrand_timeTranslate s hs] using
        (timeTranslate_integrable_Ioi hs hD)
  · intro φ
    have hT := timeTranslate_integral_Ioi_of_zero_before hs
      (fun t => ∫ x : Space, momentumTimeIntegrand u (φ.restart s hs) t x)
      (by
        intro t ht
        simp only [momentumTimeIntegrand_restart_zero s hs u φ ht, integral_zero])
    have hC := timeTranslate_integral_Ioi_of_zero_before hs
      (fun t => ∫ x : Space, momentumConvectionIntegrand u (φ.restart s hs) t x)
      (by
        intro t ht
        simp only [momentumConvectionIntegrand_restart_zero s hs u φ ht, integral_zero])
    have hD := timeTranslate_integral_Ioi_of_zero_before hs
      (fun t => ∫ x : Space, momentumDissipationIntegrand G (φ.restart s hs) t x)
      (by
        intro t ht
        simp only [momentumDissipationIntegrand_restart_zero s hs G φ ht, integral_zero])
    have heq := h.equation (φ.restart s hs)
    rw [← hT, ← hC, ← hD] at heq
    simpa only [← momentumTimeIntegrand_timeTranslate s hs,
      ← momentumConvectionIntegrand_timeTranslate s hs,
      ← momentumDissipationIntegrand_timeTranslate s hs] using heq

end MethbokeAddon.QuasiFeffermanA
