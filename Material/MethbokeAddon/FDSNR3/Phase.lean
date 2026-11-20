import MethbokeAddon.FDSN.TimePhase
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Pointwise continuous-frequency phase packets

The domain of the frequency variable is arbitrary. The multiplier is the
actual unit complex exponential, and its action is scalar multiplication
on an actual complex module. These lemmas neither assume nor assert
Fourier reconstruction, Schwartz admission, a Navier--Stokes family, or
physical force separation. Those are separate analytic endpoints.

Prepared by nonexecuting static inspection for authorized external CI.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ComplexConjugate ContDiff Topology

namespace MethbokeAddon.FDSNR3

/-- The continuous-frequency, time-localized scalar phase. -/
def packetPhase {X : Type*} (β : ℝ → ℝ) (ψ : X → ℝ)
    (lam t : ℝ) (ξ : X) : ℂ :=
  MethbokeAddon.FDSN.phase (lam * β t * ψ ξ)

/-- The compactly supported change of the scalar multiplier. -/
def packetPhaseIncrement {X : Type*} (β : ℝ → ℝ) (ψ : X → ℝ)
    (lam t : ℝ) (ξ : X) : ℂ :=
  packetPhase β ψ lam t ξ - 1

/-- The actual pointwise scalar action; no reconstruction is hidden here. -/
def packetRotate {X V : Type*} [SMul ℂ V]
    (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ) (c : X → V) : X → V :=
  fun ξ => packetPhase β ψ lam t ξ • c ξ

theorem packetPhase_eq_exp {X : Type*} (β : ℝ → ℝ) (ψ : X → ℝ)
    (lam t : ℝ) (ξ : X) :
    packetPhase β ψ lam t ξ =
      Complex.exp (((lam * β t * ψ ξ : ℝ) : ℂ) * Complex.I) := rfl

@[simp] theorem packetPhase_zero_parameter {X : Type*}
    (β : ℝ → ℝ) (ψ : X → ℝ) (t : ℝ) (ξ : X) :
    packetPhase β ψ 0 t ξ = 1 := by
  simp [packetPhase]

@[simp] theorem packetPhase_ne_zero {X : Type*}
    (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ) (ξ : X) :
    packetPhase β ψ lam t ξ ≠ 0 :=
  MethbokeAddon.FDSN.phase_ne_zero _

@[simp] theorem norm_packetPhase {X : Type*}
    (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ) (ξ : X) :
    ‖packetPhase β ψ lam t ξ‖ = 1 :=
  MethbokeAddon.FDSN.norm_phase _

/-- Odd phase is exactly the conjugacy needed by a real inverse transform. -/
theorem packetPhase_neg {X : Type*} [Neg X]
    (β : ℝ → ℝ) {ψ : X → ℝ}
    (hψ : ∀ ξ : X, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (ξ : X) :
    packetPhase β ψ lam t (-ξ) =
      conj (packetPhase β ψ lam t ξ) := by
  simp only [packetPhase, hψ ξ, mul_neg, MethbokeAddon.FDSN.phase_neg]

theorem packetPhase_eq_one_of_beta_zero {X : Type*}
    {β : ℝ → ℝ} (ψ : X → ℝ) (lam : ℝ) {t : ℝ}
    (hβ : β t = 0) (ξ : X) :
    packetPhase β ψ lam t ξ = 1 := by
  simp [packetPhase, hβ]

theorem packetPhase_eq_one_of_psi_zero {X : Type*}
    (β : ℝ → ℝ) {ψ : X → ℝ} (lam t : ℝ) {ξ : X}
    (hψ : ψ ξ = 0) :
    packetPhase β ψ lam t ξ = 1 := by
  simp [packetPhase, hψ]

theorem packetPhase_at_normalization {X : Type*}
    {β : ℝ → ℝ} {ψ : X → ℝ} (lam : ℝ) {t : ℝ} {ξ : X}
    (hβ : β t = 1) (hψ : ψ ξ = 1) :
    packetPhase β ψ lam t ξ = MethbokeAddon.FDSN.phase lam := by
  simp [packetPhase, hβ, hψ]

@[simp] theorem packetPhaseIncrement_zero_parameter {X : Type*}
    (β : ℝ → ℝ) (ψ : X → ℝ) (t : ℝ) (ξ : X) :
    packetPhaseIncrement β ψ 0 t ξ = 0 := by
  simp [packetPhaseIncrement]

theorem norm_packetPhaseIncrement_le {X : Type*}
    (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ) (ξ : X) :
    ‖packetPhaseIncrement β ψ lam t ξ‖ ≤
      ‖lam‖ * ‖β t‖ * ‖ψ ξ‖ := by
  simpa only [packetPhaseIncrement, packetPhase, norm_mul] using
    (MethbokeAddon.FDSN.norm_phase_sub_one_le (lam * β t * ψ ξ))

theorem tsupport_packetPhaseIncrement_frequency_subset
    {X : Type*} [TopologicalSpace X]
    (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ) :
    tsupport (packetPhaseIncrement β ψ lam t) ⊆ tsupport ψ := by
  change tsupport
      ((fun r : ℝ => MethbokeAddon.FDSN.phase (lam * β t * r) - 1) ∘ ψ)
    ⊆ tsupport ψ
  exact tsupport_comp_subset (by simp) ψ

theorem hasCompactSupport_packetPhaseIncrement_frequency
    {X : Type*} [TopologicalSpace X]
    (β : ℝ → ℝ) {ψ : X → ℝ} (hψ : HasCompactSupport ψ)
    (lam t : ℝ) :
    HasCompactSupport (packetPhaseIncrement β ψ lam t) := by
  change HasCompactSupport
    ((fun r : ℝ => MethbokeAddon.FDSN.phase (lam * β t * r) - 1) ∘ ψ)
  exact hψ.comp_left (by simp)

theorem tsupport_packetPhaseIncrement_time_subset
    {X : Type*} (β : ℝ → ℝ) (ψ : X → ℝ) (lam : ℝ) (ξ : X) :
    tsupport (fun t : ℝ => packetPhaseIncrement β ψ lam t ξ) ⊆ tsupport β := by
  change tsupport
      ((fun r : ℝ => MethbokeAddon.FDSN.phase (lam * r * ψ ξ) - 1) ∘ β)
    ⊆ tsupport β
  exact tsupport_comp_subset (by simp) β

theorem hasCompactSupport_packetPhaseIncrement_time
    {X : Type*} {β : ℝ → ℝ} (hβ : HasCompactSupport β)
    (ψ : X → ℝ) (lam : ℝ) (ξ : X) :
    HasCompactSupport (fun t : ℝ => packetPhaseIncrement β ψ lam t ξ) := by
  change HasCompactSupport
    ((fun r : ℝ => MethbokeAddon.FDSN.phase (lam * r * ψ ξ) - 1) ∘ β)
  exact hβ.comp_left (by simp)

section Module

variable {X V : Type*} [AddCommGroup V] [Module ℂ V]

@[simp] theorem packetRotate_zero_parameter
    (β : ℝ → ℝ) (ψ : X → ℝ) (t : ℝ) (c : X → V) :
    packetRotate β ψ 0 t c = c := by
  funext ξ
  simp [packetRotate]

theorem packetRotate_eq_of_beta_zero
    {β : ℝ → ℝ} (ψ : X → ℝ) (lam : ℝ) {t : ℝ}
    (hβ : β t = 0) (c : X → V) :
    packetRotate β ψ lam t c = c := by
  funext ξ
  simp [packetRotate, packetPhase_eq_one_of_beta_zero ψ lam hβ]

theorem packetRotate_eq_of_psi_zero
    (β : ℝ → ℝ) {ψ : X → ℝ} (lam t : ℝ) {ξ : X}
    (hψ : ψ ξ = 0) (c : X → V) :
    packetRotate β ψ lam t c ξ = c ξ := by
  simp [packetRotate, packetPhase_eq_one_of_psi_zero β lam t hψ]

theorem packetRotate_at_normalization
    {β : ℝ → ℝ} {ψ : X → ℝ} (lam : ℝ) {t : ℝ} {ξ : X}
    (hβ : β t = 1) (hψ : ψ ξ = 1) (c : X → V) :
    packetRotate β ψ lam t c ξ =
      MethbokeAddon.FDSN.phase lam • c ξ := by
  rw [packetRotate, packetPhase_at_normalization lam hβ hψ]

theorem packetRotate_sub
    (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ) (c : X → V) (ξ : X) :
    packetRotate β ψ lam t c ξ - c ξ =
      packetPhaseIncrement β ψ lam t ξ • c ξ := by
  simp only [packetRotate, packetPhaseIncrement, sub_smul, one_smul]

/-- Any actual complex-linear spectral constraint is retained pointwise. -/
theorem packetRotate_linear_kernel
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ)
    (c : X → V) (L : X → V →ₗ[ℂ] W)
    (hc : ∀ ξ : X, L ξ (c ξ) = 0) :
    ∀ ξ : X, L ξ (packetRotate β ψ lam t c ξ) = 0 := by
  intro ξ
  simp only [packetRotate, map_smul, hc ξ, smul_zero]

end Module

section Normed

variable {X V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem norm_packetRotate
    (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ) (c : X → V) (ξ : X) :
    ‖packetRotate β ψ lam t c ξ‖ = ‖c ξ‖ := by
  simp only [packetRotate, norm_smul, norm_packetPhase, one_mul]

/-- In particular, each fixed helical linear observation keeps its norm. -/
theorem norm_linearMap_packetRotate
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ)
    (c : X → V) (ξ : X) (L : V →ₗ[ℂ] W) :
    ‖L (packetRotate β ψ lam t c ξ)‖ = ‖L (c ξ)‖ := by
  simp only [packetRotate, map_smul, norm_smul, norm_packetPhase, one_mul]

theorem norm_packetRotate_sub_le
    (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ) (c : X → V) (ξ : X) :
    ‖packetRotate β ψ lam t c ξ - c ξ‖ ≤
      (‖lam‖ * ‖β t‖ * ‖ψ ξ‖) * ‖c ξ‖ := by
  rw [packetRotate_sub, norm_smul]
  exact mul_le_mul_of_nonneg_right
    (norm_packetPhaseIncrement_le β ψ lam t ξ) (norm_nonneg (c ξ))

end Normed

/-- Coordinatewise conjugacy. Apply this to each scalar coordinate of a
complex vector Fourier transform. -/
theorem packetRotate_reality {X : Type*} [Neg X]
    (β : ℝ → ℝ) {ψ : X → ℝ}
    (hψ : ∀ ξ : X, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) {c : X → ℂ}
    (hc : ∀ ξ : X, c (-ξ) = conj (c ξ)) :
    ∀ ξ : X, packetRotate β ψ lam t c (-ξ) =
      conj (packetRotate β ψ lam t c ξ) := by
  intro ξ
  change packetPhase β ψ lam t (-ξ) * c (-ξ) =
    conj (packetPhase β ψ lam t ξ * c ξ)
  rw [packetPhase_neg β hψ, hc ξ, map_mul]

/-- At an active nonzero coefficient and normalized time, distinct small
parameters yield distinct coefficients. Translation exclusion is a separate
open-patch argument. -/
theorem packetRotate_active_separates {X : Type*}
    {β : ℝ → ℝ} {ψ : X → ℝ} {t : ℝ} {ξ : X}
    (hβ : β t = 1) (hψ : ψ ξ = 1)
    {c : X → ℂ} (hc : c ξ ≠ 0) {lam eta : ℝ}
    (hlambda : |lam| < Real.pi / 4) (heta : |eta| < Real.pi / 4)
    (hne : lam ≠ eta) :
    packetRotate β ψ lam t c ξ ≠ packetRotate β ψ eta t c ξ := by
  intro h
  rw [packetRotate_at_normalization lam hβ hψ,
    packetRotate_at_normalization eta hβ hψ] at h
  change MethbokeAddon.FDSN.phase lam * c ξ =
    MethbokeAddon.FDSN.phase eta * c ξ at h
  exact hne (MethbokeAddon.FDSN.phase_injective_small hlambda heta
    (mul_right_cancel₀ hc h))

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_packetPhase_joint
    {β : ℝ → ℝ} {ψ : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞
      (fun q : ℝ × (ℝ × E) => packetPhase β ψ q.1 q.2.1 q.2.2) := by
  exact MethbokeAddon.FDSN.contDiff_phase.comp
    ((contDiff_fst.mul (hβ.comp (contDiff_fst.comp contDiff_snd))).mul
      (hψ.comp (contDiff_snd.comp contDiff_snd)))

theorem contDiff_packetPhaseIncrement_joint
    {β : ℝ → ℝ} {ψ : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞
      (fun q : ℝ × (ℝ × E) => packetPhaseIncrement β ψ q.1 q.2.1 q.2.2) :=
  (contDiff_packetPhase_joint hβ hψ).sub contDiff_const

end Smooth

end MethbokeAddon.FDSNR3

