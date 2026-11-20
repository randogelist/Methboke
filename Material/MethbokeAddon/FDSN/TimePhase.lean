import MethbokeAddon.FDSN.Phase
import MethbokeAddon.FDSN.TimeBump
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Smooth, compactly time-localized phase factors for torus FDSN

The functions in this module are actual real-time/complex-valued functions.
They are scalar ingredients of the finite Fourier-pair correction. Admission
of the periodic velocity and its Fourier coefficients remains a separate step.
-/

noncomputable section

open Set
open scoped ContDiff Topology

namespace MethbokeAddon.FDSN

/-- The phase factor used on the selected positive Fourier mode. -/
def timePhase (β : ℝ → ℝ) (lambda t : ℝ) : ℂ :=
  phase (lambda * β t)

/-- The compactly supported change of the scalar phase factor. -/
def timePhaseIncrement (β : ℝ → ℝ) (lambda t : ℝ) : ℂ :=
  timePhase β lambda t - 1

theorem contDiff_phase : ContDiff ℝ ∞ phase := by
  change ContDiff ℝ ∞ (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
  exact (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp

theorem contDiff_timePhase {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (lambda : ℝ) :
    ContDiff ℝ ∞ (timePhase β lambda) :=
  contDiff_phase.comp (contDiff_const.mul hβ)

theorem contDiff_timePhase_joint {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => timePhase β q.1 q.2) :=
  contDiff_phase.comp (contDiff_fst.mul (hβ.comp contDiff_snd))

theorem contDiff_timePhaseIncrement {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (lambda : ℝ) :
    ContDiff ℝ ∞ (timePhaseIncrement β lambda) :=
  (contDiff_timePhase hβ lambda).sub contDiff_const

theorem contDiff_timePhaseIncrement_joint {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => timePhaseIncrement β q.1 q.2) :=
  (contDiff_timePhase_joint hβ).sub contDiff_const

@[simp] theorem timePhase_zero_parameter (β : ℝ → ℝ) (t : ℝ) :
    timePhase β 0 t = 1 := by
  simp [timePhase]

@[simp] theorem timePhaseIncrement_zero_parameter (β : ℝ → ℝ) (t : ℝ) :
    timePhaseIncrement β 0 t = 0 := by
  simp [timePhaseIncrement]

theorem timePhase_at_normalization {β : ℝ → ℝ} {t : ℝ}
    (hβt : β t = 1) (lambda : ℝ) :
    timePhase β lambda t = phase lambda := by
  simp [timePhase, hβt]

theorem timePhase_eq_one_of_notMem_tsupport {β : ℝ → ℝ} {t : ℝ}
    (ht : t ∉ tsupport β) (lambda : ℝ) :
    timePhase β lambda t = 1 := by
  simp [timePhase, image_eq_zero_of_notMem_tsupport ht]

theorem tsupport_timePhaseIncrement_subset (β : ℝ → ℝ) (lambda : ℝ) :
    tsupport (timePhaseIncrement β lambda) ⊆ tsupport β := by
  change tsupport ((fun r : ℝ => phase (lambda * r) - 1) ∘ β) ⊆ tsupport β
  exact tsupport_comp_subset (by simp) β

theorem hasCompactSupport_timePhaseIncrement {β : ℝ → ℝ}
    (hβ : HasCompactSupport β) (lambda : ℝ) :
    HasCompactSupport (timePhaseIncrement β lambda) := by
  change HasCompactSupport ((fun r : ℝ => phase (lambda * r) - 1) ∘ β)
  exact hβ.comp_left (by simp)

theorem tsupport_deriv_timePhaseIncrement_subset (β : ℝ → ℝ) (lambda : ℝ) :
    tsupport (deriv (timePhaseIncrement β lambda)) ⊆ tsupport β :=
  tsupport_deriv_subset.trans (tsupport_timePhaseIncrement_subset β lambda)

theorem hasCompactSupport_deriv_timePhaseIncrement {β : ℝ → ℝ}
    (hβ : HasCompactSupport β) (lambda : ℝ) :
    HasCompactSupport (deriv (timePhaseIncrement β lambda)) :=
  (hasCompactSupport_timePhaseIncrement hβ lambda).deriv

@[simp] theorem norm_timePhase (β : ℝ → ℝ) (lambda t : ℝ) :
    ‖timePhase β lambda t‖ = 1 :=
  norm_phase _

theorem norm_timePhaseIncrement_le (β : ℝ → ℝ) (lambda t : ℝ) :
    ‖timePhaseIncrement β lambda t‖ ≤ ‖lambda‖ * ‖β t‖ := by
  calc
    ‖timePhaseIncrement β lambda t‖ ≤ ‖lambda * β t‖ :=
      norm_phase_sub_one_le _
    _ = ‖lambda‖ * ‖β t‖ := norm_mul _ _

theorem norm_timePhaseIncrement_le_parameter {β : ℝ → ℝ} {t : ℝ}
    (hβ0 : 0 ≤ β t) (hβ1 : β t ≤ 1) (lambda : ℝ) :
    ‖timePhaseIncrement β lambda t‖ ≤ ‖lambda‖ := by
  have hnorm : ‖β t‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hβ0] using hβ1
  calc
    ‖timePhaseIncrement β lambda t‖ ≤ ‖lambda‖ * ‖β t‖ :=
      norm_timePhaseIncrement_le β lambda t
    _ ≤ ‖lambda‖ * 1 := mul_le_mul_of_nonneg_left hnorm (norm_nonneg lambda)
    _ = ‖lambda‖ := mul_one _

theorem timePhase_triad_separates {β : ℝ → ℝ} {t : ℝ}
    (hβt : β t = 1) {a b c : ℂ} (hB : triadCorrelation a b c ≠ 0)
    {lambda eta : ℝ}
    (hlambda : |lambda| < Real.pi / 4) (heta : |eta| < Real.pi / 4)
    (hne : lambda ≠ eta) :
    triadCorrelation a b (timePhase β lambda t * c) ≠
      triadCorrelation a b (timePhase β eta t * c) := by
  simpa only [timePhase, hβt, mul_one] using
    (triadCorrelation_phase_separates hB hlambda heta hne)

/-- A common smooth time-localized phase family with compactly supported
increments and first derivatives, exact normalization, and a uniform
zero-order smallness estimate. This assembles K07 and the scalar support/
smoothness ingredients of K08, K11, K12 and K14. -/
theorem exists_localized_time_phase_family {s t T : ℝ}
    (hst : s < t) (htT : t < T) :
    ∃ β : ℝ → ℝ,
      ContDiff ℝ ∞ β ∧
      HasCompactSupport β ∧
      tsupport β ⊆ Ioo s T ∧
      β t = 1 ∧
      (∀ u : ℝ, 0 ≤ β u ∧ β u ≤ 1) ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℝ => timePhase β q.1 q.2) ∧
      ∀ lambda : ℝ,
        HasCompactSupport (timePhaseIncrement β lambda) ∧
        tsupport (timePhaseIncrement β lambda) ⊆ Ioo s T ∧
        tsupport (deriv (timePhaseIncrement β lambda)) ⊆ Ioo s T ∧
        ∀ u : ℝ, ‖timePhaseIncrement β lambda u‖ ≤ ‖lambda‖ := by
  obtain ⟨β, hβsmooth, hβcompact, hβsupport, hβt, hβbounds⟩ :=
    exists_normalized_time_bump hst htT
  refine ⟨β, hβsmooth, hβcompact, hβsupport, hβt, hβbounds,
    contDiff_timePhase_joint hβsmooth, ?_⟩
  intro lambda
  refine ⟨hasCompactSupport_timePhaseIncrement hβcompact lambda,
    (tsupport_timePhaseIncrement_subset β lambda).trans hβsupport,
    (tsupport_deriv_timePhaseIncrement_subset β lambda).trans hβsupport, ?_⟩
  intro u
  exact norm_timePhaseIncrement_le_parameter (hβbounds u).1 (hβbounds u).2 lambda

end MethbokeAddon.FDSN

