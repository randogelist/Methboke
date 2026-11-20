import MethbokeAddon.FDSNR3.CompactSchwartz
import MethbokeAddon.FDSNR3.NonzeroPatch
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Native local-Schwartz slice admission

The time-zero boundary is retained. The affine spatial inclusion pulls the
actual within-Taylor series on the preterminal domain back to an ordinary
Taylor series on all of space. Its operator-norm bound turns the joint
weighted bounds into the actual spatial Schwartz bounds.

No Fourier regularity or desired family conclusion is a premise.
Prepared without executing Lean locally.
-/

set_option autoImplicit false

open Set SingularClosure
open scoped BigOperators ContDiff SchwartzMap FourierTransform Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

/-- The actual spatial linear inclusion, with time component zero. -/
def spatialSliceCLM : Vec →L[ℝ] (ℝ × Vec) :=
  (0 : Vec →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Vec)

@[simp] theorem spatialSliceCLM_apply (x : Vec) :
    spatialSliceCLM x = (0, x) := rfl

/-- Spatial inclusion at a fixed physical time, as an affine map. -/
def spatialSliceAffine (t : ℝ) : Vec →ᴬ[ℝ] (ℝ × Vec) where
  toFun x := (t, x)
  linear := spatialSliceCLM.toLinearMap
  map_vadd' := by
    intro v x
    change (t, v + x) = ((0 : ℝ), v) + (t, x)
    simp
  cont := continuous_const.prodMk continuous_id

@[simp] theorem spatialSliceAffine_apply (t : ℝ) (x : Vec) :
    spatialSliceAffine t x = (t, x) := rfl

@[simp] theorem spatialSliceAffine_contLinear (t : ℝ) :
    (spatialSliceAffine t).contLinear = spatialSliceCLM := by
  ext x <;> rfl

theorem spatialSliceAffine_preimage {T t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    spatialSliceAffine t ⁻¹' preterminalSpacetime T = (univ : Set Vec) := by
  ext x
  change (t ∈ Ico (0 : ℝ) T) ↔ x ∈ (univ : Set Vec)
  simp only [ht, mem_univ]

/-- A spatial slice is genuinely smooth, including the initial slice. -/
theorem preterminal_slice_smooth {T t : ℝ} {u : Velocity}
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T))
    (ht : t ∈ Ico (0 : ℝ) T) : ContDiff ℝ ∞ (u t) := by
  have h := (hu.ftaylorSeriesWithin (uniqueDiffOn_preterminalSpacetime T)).comp_continuousAffineMap
    (spatialSliceAffine t)
  have hc := h.contDiffOn
  simpa only [spatialSliceAffine_preimage ht, contDiffOn_univ,
    Function.comp_def, spatialSliceAffine_apply] using hc

/-- All spatial derivatives are restrictions of the actual full within
derivatives along the same linear spatial inclusion. -/
theorem iteratedFDeriv_slice {T t : ℝ} {u : Velocity}
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T))
    (ht : t ∈ Ico (0 : ℝ) T) (n : ℕ) (x : Vec) :
    iteratedFDeriv ℝ n (u t) x =
      (iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (t, x)).compContinuousLinearMap
          (fun _ : Fin n => spatialSliceCLM) := by
  have hn : (n : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have h := ((hu.of_le hn).ftaylorSeriesWithin
    (uniqueDiffOn_preterminalSpacetime T)).comp_continuousAffineMap (spatialSliceAffine t)
  have huniq : UniqueDiffOn ℝ
      (spatialSliceAffine t ⁻¹' preterminalSpacetime T) := by
    rw [spatialSliceAffine_preimage ht]
    exact uniqueDiffOn_univ
  have hx : x ∈ spatialSliceAffine t ⁻¹' preterminalSpacetime T := ht
  have heq := h.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl huniq hx
  simpa only [ftaylorSeriesWithin, spatialSliceAffine_apply,
    spatialSliceAffine_contLinear, spatialSliceAffine_preimage ht,
    iteratedFDerivWithin_univ, Function.comp_def] using heq.symm

theorem norm_iteratedFDeriv_slice_le {T t : ℝ} {u : Velocity}
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T))
    (ht : t ∈ Ico (0 : ℝ) T) (n : ℕ) (x : Vec) :
    ‖iteratedFDeriv ℝ n (u t) x‖ ≤
      ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (t, x)‖ * ‖spatialSliceCLM‖ ^ n := by
  rw [iteratedFDeriv_slice hu ht]
  simpa using
    (iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T) (t, x)).norm_compContinuousLinearMap_le
        (fun _ : Fin n => spatialSliceCLM)

/-- The original local-Schwartz contract supplies actual Schwartz slices,
with no strengthened seed premise. -/
def LocalSchwartz.slice {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) : 𝓢(Vec, Vec) where
  toFun := u t
  smooth' := preterminal_slice_smooth hu.1 ht
  decay' k n := by
    obtain ⟨C, _, hC⟩ := hu.2 t ht k n
    refine ⟨C * ‖spatialSliceCLM‖ ^ n, ?_⟩
    intro x
    have hweight : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by
      gcongr
      linarith
    have hjet := norm_iteratedFDeriv_slice_le hu.1 ht n x
    have hbound := hC t ⟨ht.1, le_rfl⟩ x
    change (1 + ‖x‖) ^ k *
      ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (t, x)‖ ≤ C at hbound
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u t) x‖
          ≤ (1 + ‖x‖) ^ k *
              (‖iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
                (preterminalSpacetime T) (t, x)‖ * ‖spatialSliceCLM‖ ^ n) :=
        mul_le_mul hweight hjet (norm_nonneg _) (by positivity)
      _ = ((1 + ‖x‖) ^ k *
              ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
                (preterminalSpacetime T) (t, x)‖) * ‖spatialSliceCLM‖ ^ n := by ring
      _ ≤ C * ‖spatialSliceCLM‖ ^ n :=
        mul_le_mul_of_nonneg_right hbound (by positivity)

@[simp] theorem LocalSchwartz.slice_apply {T : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (x : Vec) :
    hu.slice ht x = u t x := rfl

theorem LocalSchwartz.exists_schwartz_slice {T : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ∃ f : 𝓢(Vec, Vec), ∀ x : Vec, f x = u t x :=
  ⟨hu.slice ht, fun _ => rfl⟩

theorem LocalSchwartz.slice_integrable {T : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    MeasureTheory.Integrable (u t) :=
  (hu.slice ht).integrable

/-- Full R3-05 endpoint: after every requested preterminal time, the
unchanged Seed supplies an actual nonzero Fourier component on an open
ball away from zero. -/
theorem Seed.exists_nonzero_fourier_ball_after
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (hseed : Seed ν T u p F)
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) T) :
    ∃ t ∈ Ioo s T, ∃ i : Fin 3, ∃ ξ₀ : Vec, ∃ r : ℝ,
      ξ₀ ≠ 0 ∧ 0 < r ∧ r < ‖ξ₀‖ ∧
      ∀ ξ ∈ Metric.ball ξ₀ r, fourierVelocity (u t) ξ i ≠ 0 := by
  obtain ⟨t, ht, x, hx⟩ := hseed.terminal_blowup.exists_nonzero_after hs
  have htime : t ∈ Ico (0 : ℝ) T :=
    ⟨le_trans hs.1 ht.1.le, ht.2⟩
  obtain ⟨i, ξ₀, r, hξ₀, hr, haway, hball⟩ :=
    physical_exists_nonzero_fourier_ball (hseed.local_schwartz.slice htime)
      (fun _ => rfl) ⟨x, hx⟩
  exact ⟨t, ht, i, ξ₀, r, hξ₀, hr, haway, hball⟩

end

end MethbokeAddon.FDSNR3

