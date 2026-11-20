import MethbokeAddon.FDSNR3.Fourier
import MethbokeAddon.FDSNR3.Phase

/-!
# An untouched open Fourier region fixes every translation

The continuous-frequency argument uses actual Euclidean translation
characters. A nonempty open frequency region on which the character is
one forces its translation vector to vanish. This yields common-time
nontranslation of the actual phase family once its Fourier formula is
identified; the formula is an explicit construction premise, not a
replacement for its separate reconstruction proof.
-/

set_option autoImplicit false

open Set SingularClosure Metric
open scoped ContDiff FourierTransform

namespace MethbokeAddon.FDSNR3

noncomputable section

/-- A Euclidean translation character cannot be one on a nonempty open
ball unless the translation is zero. The proof uses an explicit small
displacement in the translation direction and injectivity of the phase. -/
theorem translation_eq_zero_of_phase_one_on_ball
    (c y : Vec) {r : ℝ} (hr : 0 < r)
    (hphase : ∀ ξ ∈ Metric.ball c r,
      MethbokeAddon.FDSN.phase (2 * Real.pi * inner ℝ y ξ) = 1) : y = 0 := by
  by_contra hy
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let d : ℝ := min ((r / 2) / ‖y‖) ((1 / 8 : ℝ) / ‖y‖ ^ 2)
  have hd : 0 < d := by
    dsimp [d]
    apply lt_min <;> positivity
  have hd1 : d * ‖y‖ ≤ r / 2 :=
    (le_div_iff₀ hypos).mp (min_le_left _ _)
  have hd2 : d * ‖y‖ ^ 2 ≤ (1 / 8 : ℝ) :=
    (le_div_iff₀ (sq_pos_of_pos hypos)).mp (min_le_right _ _)
  have hmem : c + d • y ∈ Metric.ball c r := by
    have hdist : dist (c + d • y) c = d * ‖y‖ := by
      simp [dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
    rw [Metric.mem_ball, hdist]
    exact lt_of_le_of_lt hd1 (half_lt_self hr)
  let theta : ℝ := 2 * Real.pi * d * ‖y‖ ^ 2
  have htheta_pos : 0 < theta := by
    dsimp [theta]
    positivity
  have htheta_bound : theta ≤ Real.pi / 4 := by
    calc
      theta = (2 * Real.pi) * (d * ‖y‖ ^ 2) := by dsimp [theta]; ring
      _ ≤ (2 * Real.pi) * (1 / 8) :=
        mul_le_mul_of_nonneg_left hd2 (by positivity)
      _ = Real.pi / 4 := by ring
  have htheta_small : |theta| < Real.pi := by
    rw [abs_of_pos htheta_pos]
    linarith [Real.pi_pos]
  have hsplit : MethbokeAddon.FDSN.phase
      (2 * Real.pi * inner ℝ y (c + d • y)) =
      MethbokeAddon.FDSN.phase (2 * Real.pi * inner ℝ y c) *
        MethbokeAddon.FDSN.phase theta := by
    rw [← MethbokeAddon.FDSN.phase_add]
    congr 1
    simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    dsimp [theta]
    ring
  have hc : MethbokeAddon.FDSN.phase (2 * Real.pi * inner ℝ y c) = 1 :=
    hphase c (Metric.mem_ball_self hr)
  have hp := hphase (c + d • y) hmem
  rw [hsplit, hc, one_mul] at hp
  have hz : theta = 0 := MethbokeAddon.FDSN.phase_injective_of_abs_lt_pi
    htheta_small (by simpa using Real.pi_pos) (by simpa using hp)
  exact (ne_of_gt htheta_pos) hz

/-- Coefficient-level separation with an actual untouched open region and
one active nonzero observation. There is no triad assumption. -/
theorem packet_phase_not_translation
    {β : ℝ → ℝ} {ψ : Vec → ℝ} {t : ℝ} (hβ : β t = 1)
    (c : Vec → ℂ) (active anchor : Vec) {r : ℝ} (hr : 0 < r)
    (hactive : ψ active = 1) (hcactive : c active ≠ 0)
    (hanchor : ∀ ξ ∈ Metric.ball anchor r, ψ ξ = 0 ∧ c ξ ≠ 0)
    {lam eta : ℝ} (hlam : |lam| < Real.pi / 4)
    (heta : |eta| < Real.pi / 4) (hne : lam ≠ eta) (y : Vec) :
    ¬ ∀ ξ : Vec, packetRotate β ψ lam t c ξ =
      MethbokeAddon.FDSN.phase (2 * Real.pi * inner ℝ y ξ) *
        packetRotate β ψ eta t c ξ := by
  intro h
  have hy : y = 0 := by
    apply translation_eq_zero_of_phase_one_on_ball anchor y hr
    intro ξ hξ
    obtain ⟨hψ, hc⟩ := hanchor ξ hξ
    have hh := h ξ
    rw [packetRotate_eq_of_psi_zero β lam t hψ,
      packetRotate_eq_of_psi_zero β eta t hψ] at hh
    have he : (1 : ℂ) * c ξ =
        MethbokeAddon.FDSN.phase (2 * Real.pi * inner ℝ y ξ) * c ξ := by
      simpa only [one_mul] using hh
    exact (mul_right_cancel₀ hc he).symm
  subst y
  have hh := h active
  simp only [inner_zero_left, mul_zero, MethbokeAddon.FDSN.phase_zero, one_mul] at hh
  exact packetRotate_active_separates hβ hactive hcactive hlam heta hne hh

/-- The actual whole-space Fourier translation formula turns the open-patch
certificate into physical separation at one common time. -/
theorem translationSeparation_of_actual_packet_fourier
    (U : ℝ → Velocity) (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (c : Vec → CVec) (tstar : ℝ) (hβ : β tstar = 1)
    (i : Fin 3) (active anchor : Vec) {r : ℝ} (hr : 0 < r)
    (hactive : ψ active = 1) (hcactive : c active i ≠ 0)
    (hanchor : ∀ ξ ∈ Metric.ball anchor r, ψ ξ = 0 ∧ c ξ i ≠ 0)
    (hFourier : ∀ lam : ℝ, |lam| < Real.pi / 4 → ∀ ξ : Vec,
      fourierVelocity (U lam tstar) ξ = packetRotate β ψ lam tstar c ξ) :
    TranslationSeparation tstar (Real.pi / 4) U := by
  intro lam eta hlam heta hne
  rintro ⟨y, htranslate⟩
  apply packet_phase_not_translation hβ (fun ξ => c ξ i)
    active anchor hr hactive hcactive hanchor hlam heta hne y
  intro ξ
  have hfields : U lam tstar = (fun x : Vec => U eta tstar (x + y)) :=
    funext htranslate
  have hF := congrArg (fun v : Field => fourierVelocity v ξ) hfields
  rw [fourierVelocity_translation, hFourier lam hlam ξ,
    hFourier eta heta ξ] at hF
  have hi := congrArg (fun z : CVec => z i) hF
  simpa only [packetRotate, PiLp.smul_apply, smul_eq_mul] using hi

end

end MethbokeAddon.FDSNR3
