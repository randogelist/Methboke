import MethbokeAddon.FDSNR3.Fourier

/-!
# A nonzero open Fourier patch away from zero

This is a concrete consequence of Fourier inversion and continuity for
an actual nonzero Schwartz slice. No spectral-support hypothesis is added.
The time-selection wrapper is supplied separately by local-Schwartz admission.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure Metric
open scoped FourierTransform SchwartzMap Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

/-- A continuous scalar function nonzero somewhere is nonzero at a
nonzero point of Euclidean three-space. -/
theorem continuous_exists_nonzero_point {g : Vec → ℂ}
    (hg : Continuous g) {x : Vec} (hx : g x ≠ 0) :
    ∃ y : Vec, y ≠ 0 ∧ g y ≠ 0 := by
  by_cases hx0 : x = 0
  · subst x
    have hn : {y : Vec | g y ≠ 0} ∈ 𝓝 (0 : Vec) :=
      (isOpen_ne hg continuous_const).mem_nhds hx
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
    let y : Vec := (r / 2) • unitVector (0 : Fin 3)
    have hyn : ‖y‖ = r / 2 := by
      simp [y, norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hr), unitVector]
    have hy0 : y ≠ 0 := by
      apply norm_pos_iff.mp
      rw [hyn]
      exact half_pos hr
    refine ⟨y, hy0, hball ?_⟩
    rw [Metric.mem_ball, dist_zero_right, hyn]
    exact half_lt_self hr
  · exact ⟨x, hx0, hx⟩

/-- A continuous nonzero observation has a whole ball of nonvanishing,
with radius smaller than the distance of its center from the origin. -/
theorem continuous_exists_nonzero_ball {g : Vec → ℂ}
    (hg : Continuous g) {x : Vec} (hx : g x ≠ 0) :
    ∃ ξ₀ : Vec, ∃ r : ℝ,
      ξ₀ ≠ 0 ∧ 0 < r ∧ r < ‖ξ₀‖ ∧
      ∀ ξ ∈ Metric.ball ξ₀ r, g ξ ≠ 0 := by
  obtain ⟨ξ₀, hξ₀, hgξ₀⟩ := continuous_exists_nonzero_point hg hx
  have hn : {ξ : Vec | g ξ ≠ 0} ∈ 𝓝 ξ₀ :=
    (isOpen_ne hg continuous_const).mem_nhds hgξ₀
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hn
  have hnorm : 0 < ‖ξ₀‖ := norm_pos_iff.mpr hξ₀
  refine ⟨ξ₀, min (d / 2) (‖ξ₀‖ / 2), hξ₀,
    lt_min (half_pos hd) (half_pos hnorm), ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hnorm)
  · intro ξ hξ
    apply hball
    have hrle : min (d / 2) (‖ξ₀‖ / 2) ≤ d :=
      le_trans (min_le_left _ _) (half_le_self hd.le)
    exact lt_of_lt_of_le hξ hrle

/-- Every nonzero complex Schwartz field has a nonzero component on an
open frequency ball that stays away from the origin. -/
theorem schwartz_exists_nonzero_fourier_ball
    (f : 𝓢(Vec, CVec)) (hf : f ≠ 0) :
    ∃ i : Fin 3, ∃ ξ₀ : Vec, ∃ r : ℝ,
      ξ₀ ≠ 0 ∧ 0 < r ∧ r < ‖ξ₀‖ ∧
      ∀ ξ ∈ Metric.ball ξ₀ r, (𝓕 f ξ) i ≠ 0 := by
  have hF : 𝓕 f ≠ (0 : 𝓢(Vec, CVec)) := by
    intro h
    apply hf
    apply schwartz_fourier_injective
    simpa only [FourierTransform.fourier_zero] using h
  have hex : ∃ x : Vec, ∃ i : Fin 3, (𝓕 f x) i ≠ 0 := by
    by_contra! h
    apply hF
    apply SchwartzMap.ext
    intro x
    ext i
    exact h x i
  obtain ⟨x, i, hxi⟩ := hex
  have hc : Continuous (fun ξ : Vec => (𝓕 f ξ) i) :=
    (EuclideanSpace.proj i : CVec →L[ℂ] ℂ).continuous.comp (𝓕 f).continuous
  obtain ⟨ξ₀, r, hξ₀, hr, haway, hball⟩ :=
    continuous_exists_nonzero_ball hc hxi
  exact ⟨i, ξ₀, r, hξ₀, hr, haway, hball⟩

/-- Nontrivial real Schwartz data stay nontrivial under complexification. -/
theorem complexifySchwartz_ne_zero {f : 𝓢(Vec, Vec)} (hf : f ≠ 0) :
    complexifySchwartz f ≠ 0 := by
  intro h
  apply hf
  apply SchwartzMap.ext
  intro x
  have hx := congrArg (fun g : 𝓢(Vec, CVec) => realify (g x)) h
  simpa [complexifySchwartz_apply, realify_complexify, realify] using hx

/-- Physical version of the nonzero-frequency-patch conclusion. -/
theorem real_schwartz_exists_nonzero_fourier_ball
    (f : 𝓢(Vec, Vec)) (hf : f ≠ 0) :
    ∃ i : Fin 3, ∃ ξ₀ : Vec, ∃ r : ℝ,
      ξ₀ ≠ 0 ∧ 0 < r ∧ r < ‖ξ₀‖ ∧
      ∀ ξ ∈ Metric.ball ξ₀ r, fourierVelocity f ξ i ≠ 0 := by
  simpa only [fourierVelocity_eq_schwartz] using
    schwartz_exists_nonzero_fourier_ball (complexifySchwartz f)
      (complexifySchwartz_ne_zero hf)

/-- This wrapper connects an explicit Schwartz representative to the
original native physical field. It assumes no spectral information. -/
theorem physical_exists_nonzero_fourier_ball {v : Field}
    (f : 𝓢(Vec, Vec)) (hfv : ∀ x : Vec, f x = v x)
    (hv : ∃ x : Vec, v x ≠ 0) :
    ∃ i : Fin 3, ∃ ξ₀ : Vec, ∃ r : ℝ,
      ξ₀ ≠ 0 ∧ 0 < r ∧ r < ‖ξ₀‖ ∧
      ∀ ξ ∈ Metric.ball ξ₀ r, fourierVelocity v ξ i ≠ 0 := by
  have hf : f ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := hv
    apply hx
    rw [← hfv x, h]
    rfl
  have heq : (f : Vec → Vec) = v := funext hfv
  simpa only [heq] using real_schwartz_exists_nonzero_fourier_ball f hf

/-- Radius separation explicitly excludes zero from the closed ball. -/
theorem zero_notMem_closedBall_of_radius_lt_norm {ξ₀ : Vec} {r : ℝ}
    (hr : r < ‖ξ₀‖) : (0 : Vec) ∉ Metric.closedBall ξ₀ r := by
  simpa only [Metric.mem_closedBall, dist_zero_left, not_le] using hr

end

end MethbokeAddon.FDSNR3

