import MethbokeAddon.FDSN.FamilyContracts
import MethbokeAddon.FDSN.FamilySmallness
import MethbokeAddon.FDSN.LocalizedResidual
import MethbokeAddon.FDSN.LocalizedFront

/-!
# Literal FDSN clauses for the one concrete localized pair family

Both compact corrections and the preserved terminal blowup belong to the
same velocity/force pair. Helical preservation specializes the established
norm preservation for every complex-linear modal observation.
-/

set_option autoImplicit false

open Set SingularClosure
open scoped BigOperators ContDiff Topology

namespace MethbokeAddon.FDSN

noncomputable section

theorem localizedPairVelocity_compactCorrection
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (k : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) (hβ0 : tsupport β ⊆ Ioo (0 : ℝ) T)
    (a b : ℝ) (hβI : tsupport β ⊆ Ioo a b) (lambda : ℝ) :
    CompactTemporalCorrection a b (localizedPairVelocity k β u lambda - u) := by
  rw [localizedPairVelocity_sub_eq_correction]
  exact ⟨localizedPairCorrection_smooth h k hβ hβ0 lambda,
    localizedPairCorrection_periodic k β u lambda,
    localizedPairCorrection_hasCompactSupport k hβc u lambda,
    (localizedPairCorrection_tsupport_subset k β u lambda).trans hβI⟩

theorem localizedPairForce_compactCorrection
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (k : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) (hβ0 : tsupport β ⊆ Ioo (0 : ℝ) T)
    (a b : ℝ) (hβI : tsupport β ⊆ Ioo a b) (lambda : ℝ) :
    CompactTemporalCorrection a b (localizedPairForce ν k β u F lambda - F) := by
  have hmap : ContDiff ℝ ∞ (fun z : ℝ × Vec => (lambda, z)) :=
    contDiff_const.prodMk contDiff_id
  exact ⟨(localizedPairForceCorrection_joint_smooth h k hβ hβ0).comp hmap,
    localizedPairForceCorrection_periodic h k hβ hβc hβ0 lambda,
    localizedPairForceCorrection_hasCompactSupport ν k hβc u F lambda,
    (localizedPairForceCorrection_tsupport_subset ν k β u F lambda).trans hβI⟩

theorem localizedPairVelocity_terminal_blowup
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (k : Frequency) {β : ℝ → ℝ} (a b : ℝ) (hbT : b < T)
    (hβI : tsupport β ⊆ Ioo a b) (lambda : ℝ) :
    CofinalVelocityBlowup T (localizedPairVelocity k β u lambda) := by
  apply cofinalVelocityBlowup_of_late_eq hbT h.terminal_blowup
  intro t ht
  apply localizedPairVelocity_eq_seed_off_support k u lambda
  intro hts
  exact (not_lt_of_ge ht.1.le) (hβI hts).2

/-- Both helicities at every nonzero frequency, and the complete zero mode,
are preserved. No property of the coordinate array is needed for this
stronger endpoint; genuine frames are included by explicit specialization. -/
theorem localizedPairVelocity_helicalPower
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (frame : HelicalFrameArray) {k : Frequency} (hk : k ≠ 0)
    (β : ℝ → ℝ) (ε : ℝ) :
    CompleteHelicalPowerPreservation frame T ε u (localizedPairVelocity k β u) := by
  intro lambda _ t ht
  constructor
  · intro q _ σ
    unfold helicalCoefficient
    rw [localizedPairVelocity_eq_physicalPairRotation h hk β lambda t ht]
    simp only [Complex.normSq_eq_norm_sq]
    exact congrArg (fun r : ℝ => r ^ 2)
      (physicalPairRotation_observable_norm hk (norm_timePhase β lambda t)
        (h.velocity_slice_smooth t ht) (h.front.velocity_periodic t ht)
        q (helicalObservation (frame q σ)))
  · rw [localizedPairVelocity_eq_physicalPairRotation h hk β lambda t ht]
    exact physicalPairRotation_mean_coeff hk (norm_timePhase β lambda t)
      (h.velocity_slice_smooth t ht) (h.front.velocity_periodic t ht)

theorem localizedPair_family_smallness
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (k : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : tsupport β ⊆ Ioo (0 : ℝ) T)
    (a b ε : ℝ) (hab : a ≤ b) :
    SmoothSmallness a b ε u F
      (localizedPairVelocity k β u) (localizedPairForce ν k β u F) := by
  apply smooth_corrections_imply_smallness a b ε hab u F
    (localizedPairVelocity k β u) (localizedPairForce ν k β u F)
  · simpa only [localizedPairVelocity_sub_eq_correction] using
      localizedPairCorrection_joint_smooth h k hβ hβ0
  · exact localizedPairForceCorrection_joint_smooth h k hβ hβ0
  · exact localizedPairVelocity_zero_parameter k β u
  · exact localizedPairForce_zero_parameter ν k β u F

/-- Exact forced NSE admission, compact corrections, the same initial datum
and pressure, and the same terminal blowup for every parameter member. -/
theorem localizedPair_exactRealization
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {k : Frequency} (hk : k ≠ 0) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) (hβ0 : tsupport β ⊆ Ioo (0 : ℝ) T)
    (a b ε : ℝ) (hbT : b < T) (hβI : tsupport β ⊆ Ioo a b) :
    ExactRealizationAndAgreement ν T a b ε u p F
      (localizedPairVelocity k β u) (localizedPairForce ν k β u F) := by
  intro lambda _
  exact ⟨localizedPair_front h hk hβ hβ0 lambda,
    localizedPairForce_admissible h k hβ hβc hβ0 lambda,
    localizedPairVelocity_initial k hβ0 u lambda,
    localizedPairVelocity_compactCorrection h k hβ hβc hβ0 a b hβI lambda,
    localizedPairForce_compactCorrection h k hβ hβc hβ0 a b hβI lambda,
    localizedPairVelocity_terminal_blowup h k a b hbT hβI lambda⟩

end

end MethbokeAddon.FDSN
