import MethbokeAddon.FDSN.FiniteCorrection
import MethbokeAddon.FDSN.CoefficientSmooth
import MethbokeAddon.FDSN.LocalizedCoefficient

/-!
# An actual jointly smooth time-localized Fourier-pair velocity family

Only the selected actual Fourier coefficient is used.  Multiplication by
the compact phase increment makes its arbitrary total-function extension
outside the preterminal interval irrelevant to global correction smoothness.
-/

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace MethbokeAddon.FDSN

open SingularClosure

noncomputable section

def localizedPairCorrection (a : Frequency) (β : ℝ → ℝ) (u : Velocity)
    (lambda : ℝ) : Velocity :=
  fun t => physicalPairCorrection a (timePhase β lambda t) (u t)

def localizedPairVelocity (a : Frequency) (β : ℝ → ℝ) (u : Velocity)
    (lambda : ℝ) : Velocity := u + localizedPairCorrection a β u lambda

theorem Seed.velocity_slice_smooth {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (h : Seed ν T u p F) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ (u t) := by
  simpa only [Function.comp_def] using
    h.front.velocity_smooth.comp_contDiff
      (contDiff_const.prodMk contDiff_id) (fun _ => ht)

/-- Joint smoothness in the deformation parameter, all real times and space. -/
theorem localizedPairCorrection_joint_smooth {ν T : ℝ} {u F : Velocity}
    {p : Pressure} (h : Seed ν T u p F) (a : Frequency)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      localizedPairCorrection a β u q.1 q.2.1 q.2.2) := by
  apply (contDiff_piLp 2).2
  intro i
  have hproj : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Vec) => (q.1, q.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hc := (contDiff_timePhaseIncrement_mul_localCoefficient_joint hβ
    (h.fourierCoeff_contDiffOn a i) hβs).comp hproj
  have hchar : ContDiff ℝ ∞
      (fun q : ℝ × (ℝ × Vec) => fourierCharacter a q.2.2) :=
    (fourierCharacter_contDiff a).comp (contDiff_snd.comp contDiff_snd)
  exact contDiff_const.mul (Complex.reCLM.contDiff.comp (hchar.mul hc))

theorem localizedPairCorrection_smooth {ν T : ℝ} {u F : Velocity}
    {p : Pressure} (h : Seed ν T u p F) (a : Frequency)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T) (lambda : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × Vec => localizedPairCorrection a β u lambda z.1 z.2) := by
  exact (localizedPairCorrection_joint_smooth h a hβ hβs).comp
    (contDiff_const.prodMk contDiff_id)

theorem localizedPairCorrection_zero_parameter (a : Frequency)
    (β : ℝ → ℝ) (u : Velocity) : localizedPairCorrection a β u 0 = 0 := by
  funext t
  simp [localizedPairCorrection, physicalPairCorrection_one]

theorem localizedPairCorrection_eq_zero_off_support (a : Frequency)
    {β : ℝ → ℝ} (u : Velocity) (lambda : ℝ) {t : ℝ}
    (ht : t ∉ tsupport β) : localizedPairCorrection a β u lambda t = 0 := by
  simp only [localizedPairCorrection, timePhase_eq_one_of_notMem_tsupport ht,
    physicalPairCorrection_one]

theorem localizedPairCorrection_tsupport_subset (a : Frequency)
    (β : ℝ → ℝ) (u : Velocity) (lambda : ℝ) :
    tsupport (localizedPairCorrection a β u lambda) ⊆ tsupport β := by
  apply closure_minimal ?_ isClosed_tsupport
  intro t ht
  by_contra h
  exact ht (localizedPairCorrection_eq_zero_off_support a u lambda h)

theorem localizedPairCorrection_hasCompactSupport (a : Frequency)
    {β : ℝ → ℝ} (hβ : HasCompactSupport β) (u : Velocity) (lambda : ℝ) :
    HasCompactSupport (localizedPairCorrection a β u lambda) :=
  hβ.isCompact.of_isClosed_subset isClosed_tsupport
    (localizedPairCorrection_tsupport_subset a β u lambda)

theorem localizedPairCorrection_periodic (a : Frequency)
    (β : ℝ → ℝ) (u : Velocity) (lambda t : ℝ) :
    SpatialPeriodic (localizedPairCorrection a β u lambda t) :=
  physicalPairCorrection_periodic a (timePhase β lambda t) (u t)

theorem localizedPairVelocity_zero_parameter (a : Frequency)
    (β : ℝ → ℝ) (u : Velocity) : localizedPairVelocity a β u 0 = u := by
  rw [localizedPairVelocity, localizedPairCorrection_zero_parameter, add_zero]

theorem localizedPairVelocity_eq_seed_off_support (a : Frequency)
    {β : ℝ → ℝ} (u : Velocity) (lambda : ℝ) {t : ℝ}
    (ht : t ∉ tsupport β) : localizedPairVelocity a β u lambda t = u t := by
  change u t + localizedPairCorrection a β u lambda t = u t
  rw [localizedPairCorrection_eq_zero_off_support a u lambda ht, add_zero]

theorem localizedPairVelocity_initial {T : ℝ} (a : Frequency)
    {β : ℝ → ℝ} (hβs : tsupport β ⊆ Ioo (0 : ℝ) T)
    (u : Velocity) (lambda : ℝ) : localizedPairVelocity a β u lambda 0 = u 0 := by
  apply localizedPairVelocity_eq_seed_off_support a u lambda
  intro ht
  exact (lt_irrefl (0 : ℝ)) (hβs ht).1

/-- At every preterminal time, the finite correction is exactly the genuine
Fourier rotation, with no field-identification premise assumed. -/
theorem localizedPairVelocity_eq_physicalPairRotation
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) (β : ℝ → ℝ) (lambda t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) T) :
    localizedPairVelocity a β u lambda t =
      physicalPairRotation a (timePhase β lambda t) (u t) := by
  exact (physicalPairRotation_eq_add_correction ha (timePhase β lambda t)
    (h.velocity_slice_smooth t ht) (h.front.velocity_periodic t ht)).symm

theorem localizedPairVelocity_joint_smooth {ν T : ℝ} {u F : Velocity}
    {p : Pressure} (h : Seed ν T u p F) (a : Frequency)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      localizedPairVelocity a β u q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ico (0 : ℝ) T} := by
  exact (h.front.velocity_smooth.comp contDiffOn_snd (fun _ hq => hq)).add
    (localizedPairCorrection_joint_smooth h a hβ hβs).contDiffOn

/-- A constructed preterminal velocity family with the complete spatial
modal power invariants (in fact, every linear modal-observation norm). -/
theorem LOCALIZED_PAIR_VELOCITY_PRESERVES_SPECTRAL_DATA
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) (β : ℝ → ℝ) (lambda t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ (localizedPairVelocity a β u lambda t) ∧
    SpatialPeriodic (localizedPairVelocity a β u lambda t) ∧
    (∀ x : Vec, divergence (localizedPairVelocity a β u lambda t) x = 0) ∧
    spatialMean (localizedPairVelocity a β u lambda t) = spatialMean (u t) ∧
    (∀ k : Frequency, ∀ L : (Fin 3 → ℂ) →ₗ[ℂ] ℂ,
      ‖L (datumFourierCoeff (localizedPairVelocity a β u lambda t) k)‖ =
        ‖L (datumFourierCoeff (u t) k)‖) := by
  rw [localizedPairVelocity_eq_physicalPairRotation h ha β lambda t ht]
  exact PHYSICAL_PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_DATA ha
    (norm_timePhase β lambda t) (h.velocity_slice_smooth t ht)
    (h.front.velocity_periodic t ht) (h.front.divergence_free t ht)

end

end MethbokeAddon.FDSN
