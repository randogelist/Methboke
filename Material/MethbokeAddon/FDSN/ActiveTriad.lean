import MethbokeAddon.FDSN.ForcedFourierEvolution
import MethbokeAddon.FDSN.ModeEnvelope
import MethbokeAddon.FDSN.UniformForceDecay
import MethbokeAddon.FDSN.PointwiseEnvelope

/-!
# An active noncollinear Fourier triad in every final interval

Absence of an active triad removes modal nonlinear energy transfer. The
actual smooth force has a common summable Fourier envelope, and scalar
Gronwall propagates the envelope of one strictly preterminal velocity slice.
Fourier reconstruction then contradicts the Seed's cofinal physical blowup.
The argument retains the zero mode and needs no final-time velocity value.
-/

set_option autoImplicit false

open Set SingularClosure
open scoped BigOperators ContDiff

namespace MethbokeAddon.FDSN

noncomputable section

theorem Seed.uniform_fourier_envelope_of_no_active_triad
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) T)
    (htriad : ∀ t ∈ Ico a T,
      ¬ HasActiveNoncollinearTriad (datumFourierCoeff (u t))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico a T, ∀ k : Frequency, ∀ i : Fin 3,
      ‖datumFourierCoeff (u t) k i‖ ≤ C * (torusSobolevWeight k)⁻¹ ^ 4 := by
  obtain ⟨C₀, hC₀, h₀⟩ := smoothPeriodic_exists_fourier_envelope
    (h.front.velocity_slice_smooth a ha)
    (h.front.velocity_periodic a ⟨ha.1.le, ha.2⟩)
  obtain ⟨C₁, hC₁, h₁⟩ := admissibleForce_uniform_fourier_envelope h.force T
  let B : ℝ := (C₀ ^ 2 + 3 * C₁ ^ 2) * Real.exp (T - a)
  have hB : 0 ≤ B := mul_nonneg (add_nonneg (sq_nonneg C₀)
    (mul_nonneg (by norm_num) (sq_nonneg C₁))) (Real.exp_pos _).le
  refine ⟨Real.sqrt B, Real.sqrt_nonneg B, ?_⟩
  intro t ht k i
  apply weighted_norm_le_of_normSq_le hB
  apply uniform_energy_bound_of_deriv_le
    (E := fun r => Complex.normSq (datumFourierCoeff (u r) k i))
    (a := a) (T := T) (A := C₀ ^ 2) (G := 3 * C₁ ^ 2)
    (ρ := (torusSobolevWeight k)⁻¹ ^ 8)
    (sq_nonneg C₀) (mul_nonneg (by norm_num) (sq_nonneg C₁)) (by positivity)
    ?_ (complex_normSq_le_of_weighted_norm_le (h₀ k i)) ?_ t ht
  · intro r hr
    have hr0 : r ∈ Ioo (0 : ℝ) T := ⟨lt_of_lt_of_le ha.1 hr.1, hr.2⟩
    exact (complex_normSq_hasDerivAt
      (h.front.fourierCoeff_hasDerivAt r hr0 k i)).differentiableAt
  · intro r hr
    have hr0 : r ∈ Ioo (0 : ℝ) T := ⟨lt_of_lt_of_le ha.1 hr.1, hr.2⟩
    have hFs : ContDiff ℝ ∞ (F r) :=
      h.force.smooth.comp (contDiff_const.prodMk contDiff_id)
    have hproj := coefficientLeray_component_normSq_le_envelope
      k (datumFourierCoeff (F r) k) C₁
      (h₁ r ⟨hr0.1.le, hr0.2.le⟩ k) i
    exact (h.front.triad_free_mode_energy_bound h.viscosity_pos.le r hr0
      hFs.continuous (htriad r hr) k i).trans (add_le_add_left hproj _)

/-- The active-triad seed for the nontranslation certificate can be chosen
inside every final interval. This conclusion is derived from the actual
forced PDE, force smoothness, and the cofinal physical blowup in Seed. -/
theorem Seed.exists_active_noncollinear_triad_after
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (s : ℝ) (hs : s ∈ Ico (0 : ℝ) T) :
    ∃ t ∈ Ioo s T, HasActiveNoncollinearTriad (datumFourierCoeff (u t)) := by
  classical
  by_contra hnone
  let a : ℝ := (s + T) / 2
  have hsa : s < a := by dsimp [a]; linarith [hs.2]
  have haT : a < T := by dsimp [a]; linarith [hs.2]
  have ha0 : 0 < a := lt_of_le_of_lt hs.1 hsa
  have htriad : ∀ t ∈ Ico a T,
      ¬ HasActiveNoncollinearTriad (datumFourierCoeff (u t)) := by
    intro t ht httriad
    exact hnone ⟨t, ⟨lt_of_lt_of_le hsa ht.1, ht.2⟩, httriad⟩
  obtain ⟨C, hC, henv⟩ := h.uniform_fourier_envelope_of_no_active_triad
    a ⟨ha0, haT⟩ htriad
  apply h.no_final_uniform_fourier_envelope a ⟨ha0.le, haT⟩
  exact ⟨C, hC, fun t ht => henv t ⟨ht.1.le, ht.2⟩⟩

end

end MethbokeAddon.FDSN
