import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar phase and triad-correlation leaves for torus FDSN

These are coefficient-level lemmas. Admission of the actual periodic
velocity and identification of its Fourier coefficients are separate
endpoints. No PDE hypothesis or desired family conclusion is assumed here.
-/

noncomputable section

open scoped ComplexConjugate

namespace MethbokeAddon.FDSN

/-- The real one-parameter unit complex phase. -/
def phase (theta : ℝ) : ℂ := Complex.exp ((theta : ℂ) * Complex.I)

@[simp] theorem phase_zero : phase 0 = 1 := by
  simp [phase]

theorem phase_add (theta eta : ℝ) :
    phase (theta + eta) = phase theta * phase eta := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

@[simp] theorem phase_ne_zero (theta : ℝ) : phase theta ≠ 0 :=
  Complex.exp_ne_zero _

@[simp] theorem norm_phase (theta : ℝ) : ‖phase theta‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I theta

theorem phase_neg (theta : ℝ) : phase (-theta) = conj (phase theta) := by
  simp only [phase, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Complex.ofReal_neg, neg_mul, mul_neg]

theorem conj_phase (theta : ℝ) : conj (phase theta) = phase (-theta) :=
  (phase_neg theta).symm

@[simp] theorem phase_mul_neg (theta : ℝ) : phase theta * phase (-theta) = 1 := by
  rw [← phase_add, add_neg_cancel, phase_zero]

@[simp] theorem norm_phase_mul (theta : ℝ) (z : ℂ) :
    ‖phase theta * z‖ = ‖z‖ := by
  rw [norm_mul, norm_phase, one_mul]

@[simp] theorem modal_power_phase_mul (theta : ℝ) (z : ℂ) :
    ‖phase theta * z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [norm_phase_mul]

theorem norm_phase_sub_one_le (theta : ℝ) :
    ‖phase theta - 1‖ ≤ ‖theta‖ := by
  simpa only [phase, mul_comm] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := theta))

theorem norm_phase_mul_sub_le (theta : ℝ) (z : ℂ) :
    ‖phase theta * z - z‖ ≤ ‖theta‖ * ‖z‖ := by
  calc
    ‖phase theta * z - z‖ = ‖(phase theta - 1) * z‖ := by
      congr 1
      ring
    _ = ‖phase theta - 1‖ * ‖z‖ := norm_mul _ _
    _ ≤ ‖theta‖ * ‖z‖ :=
      mul_le_mul_of_nonneg_right (norm_phase_sub_one_le theta) (norm_nonneg z)

theorem phase_injective_of_abs_lt_pi {theta eta : ℝ}
    (htheta : |theta| < Real.pi) (heta : |eta| < Real.pi)
    (h : phase theta = phase eta) : theta = eta := by
  have he : (theta : ℂ) * Complex.I = (eta : ℂ) * Complex.I :=
    Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (by simpa using (abs_lt.mp htheta).1)
      (by simpa using (abs_lt.mp htheta).2.le)
      (by simpa using (abs_lt.mp heta).1)
      (by simpa using (abs_lt.mp heta).2.le) h
  simpa using congrArg Complex.im he

theorem phase_injective_small {theta eta : ℝ}
    (htheta : |theta| < Real.pi / 4) (heta : |eta| < Real.pi / 4)
    (h : phase theta = phase eta) : theta = eta := by
  have hquarter : Real.pi / 4 < Real.pi := by linarith [Real.pi_pos]
  exact phase_injective_of_abs_lt_pi
    (lt_trans htheta hquarter) (lt_trans heta hquarter) h

/-- The scalar correlation attached to a resonant triad k1+k2=k3. -/
def triadCorrelation (a b c : ℂ) : ℂ := a * b * conj c

theorem triadCorrelation_ne_zero {a b c : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    triadCorrelation a b c ≠ 0 := by
  have hconj : conj c ≠ 0 := by
    intro h
    apply hc
    have hh := congrArg (starRingEnd ℂ) h
    simpa using hh
  exact mul_ne_zero (mul_ne_zero ha hb) hconj

theorem triadCorrelation_phase (a b c : ℂ) (theta : ℝ) :
    triadCorrelation a b (phase theta * c) =
      phase (-theta) * triadCorrelation a b c := by
  simp only [triadCorrelation, map_mul, conj_phase]
  ring

/-- Translation characters on a resonant triad have angles alpha, beta,
and alpha+beta, so they preserve the correlation. -/
theorem triadCorrelation_translation (a b c : ℂ) (alpha beta : ℝ) :
    triadCorrelation (phase alpha * a) (phase beta * b)
      (phase (alpha + beta) * c) = triadCorrelation a b c := by
  simp only [triadCorrelation, map_mul, conj_phase]
  calc
    (phase alpha * a) * (phase beta * b) * (phase (-(alpha + beta)) * conj c)
        = (phase alpha * phase beta * phase (-(alpha + beta))) *
            (a * b * conj c) := by ring
    _ = a * b * conj c := by rw [← phase_add, phase_mul_neg, one_mul]

theorem triadCorrelation_phase_separates {a b c : ℂ}
    (hB : triadCorrelation a b c ≠ 0) {lambda eta : ℝ}
    (hlambda : |lambda| < Real.pi / 4) (heta : |eta| < Real.pi / 4)
    (hne : lambda ≠ eta) :
    triadCorrelation a b (phase lambda * c) ≠
      triadCorrelation a b (phase eta * c) := by
  intro h
  rw [triadCorrelation_phase, triadCorrelation_phase] at h
  have hp : phase (-lambda) = phase (-eta) := mul_right_cancel₀ hB h
  have hn : -lambda = -eta := phase_injective_small
    (by simpa only [abs_neg] using hlambda)
    (by simpa only [abs_neg] using heta) hp
  exact hne (neg_injective hn)

/-- No translation-character triple can identify distinct members of the
one-mode phase family when the triad correlation is nonzero. This is the
coefficient-level nontranslation endpoint; the actual Fourier adapter
supplies the translation characters of a periodic velocity. -/
theorem triad_phase_not_translation {a b c : ℂ}
    (hB : triadCorrelation a b c ≠ 0) {lambda eta : ℝ}
    (hlambda : |lambda| < Real.pi / 4) (heta : |eta| < Real.pi / 4)
    (hne : lambda ≠ eta) (alpha beta : ℝ) :
    ¬ (phase alpha * a = a ∧ phase beta * b = b ∧
      phase (alpha + beta) * (phase lambda * c) = phase eta * c) := by
  rintro ⟨ha, hb, hc⟩
  have ht := triadCorrelation_translation a b (phase lambda * c) alpha beta
  rw [ha, hb, hc] at ht
  exact triadCorrelation_phase_separates hB hlambda heta hne ht.symm

end MethbokeAddon.FDSN
