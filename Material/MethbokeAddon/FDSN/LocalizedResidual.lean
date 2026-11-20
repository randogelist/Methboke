import MethbokeAddon.FDSN.JointResidual
import MethbokeAddon.FDSN.LocalizedPair

/-!
# The concrete forcing family for the localized Fourier-pair deformation
-/

set_option autoImplicit false

noncomputable section

open Set SingularClosure
open MethbokeAddon.WeakFouriermanB MethbokeAddon.FeffermanFamily
open scoped ContDiff Topology

namespace MethbokeAddon.FDSN

def localizedPairForce (ν : ℝ) (a : Frequency) (β : ℝ → ℝ)
    (u F : Velocity) (lambda : ℝ) : Velocity :=
  residualForce ν u F (localizedPairCorrection a β u lambda)

theorem localizedPairVelocity_sub_eq_correction
    (a : Frequency) (β : ℝ → ℝ) (u : Velocity) (lambda : ℝ) :
    localizedPairVelocity a β u lambda - u = localizedPairCorrection a β u lambda := by
  exact add_sub_cancel_left u (localizedPairCorrection a β u lambda)

theorem localizedPairForce_zero_parameter
    (ν : ℝ) (a : Frequency) (β : ℝ → ℝ) (u F : Velocity) :
    localizedPairForce ν a β u F 0 = F := by
  rw [localizedPairForce, localizedPairCorrection_zero_parameter, residualForce_zero_correction]

theorem localizedPairForce_joint_smooth
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      localizedPairForce ν a β u F q.1 q.2.1 q.2.2) := by
  have hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T) :=
    h.front.velocity_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)
  exact residualForce_joint_contDiff_of_common_timeSupport ν u F
    (localizedPairCorrection a β u) T hU h.force.smooth
    (localizedPairCorrection_joint_smooth h a hβ hβs).contDiffOn
    (tsupport β) (isClosed_tsupport β) hβs
    (localizedPairCorrection_tsupport_subset a β u)

theorem localizedPairForceCorrection_joint_smooth
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      (localizedPairForce ν a β u F q.1 - F) q.2.1 q.2.2) :=
  (localizedPairForce_joint_smooth h a hβ hβs).sub (h.force.smooth.comp contDiff_snd)

theorem localizedPairForceCorrection_tsupport_subset
    (ν : ℝ) (a : Frequency) (β : ℝ → ℝ) (u F : Velocity) (lambda : ℝ) :
    tsupport (localizedPairForce ν a β u F lambda - F) ⊆ tsupport β :=
  (tsupport_residualForce_sub_subset ν u F (localizedPairCorrection a β u lambda)).trans
    (localizedPairCorrection_tsupport_subset a β u lambda)

theorem localizedPairForceCorrection_hasCompactSupport
    (ν : ℝ) (a : Frequency) {β : ℝ → ℝ} (hβ : HasCompactSupport β)
    (u F : Velocity) (lambda : ℝ) :
    HasCompactSupport (localizedPairForce ν a β u F lambda - F) :=
  hβ.isCompact.of_isClosed_subset (isClosed_tsupport _)
    (localizedPairForceCorrection_tsupport_subset ν a β u F lambda)

theorem localizedPairForce_admissible
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) (hβs : tsupport β ⊆ Ioo (0 : ℝ) T)
    (lambda : ℝ) :
    AdmissiblePeriodicForce (localizedPairForce ν a β u F lambda) := by
  apply admissiblePeriodicForce_residual ν u F (localizedPairCorrection a β u lambda)
    T h.force
  · exact h.front.velocity_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)
  · exact (localizedPairCorrection_smooth h a hβ hβs lambda).contDiffOn
  · intro t ht
    exact h.front.velocity_periodic t ⟨ht.1.le, ht.2⟩
  · intro t _
    exact localizedPairCorrection_periodic a β u lambda t
  · exact localizedPairCorrection_hasCompactSupport a hβc u lambda
  · exact (localizedPairCorrection_tsupport_subset a β u lambda).trans hβs

theorem localizedPairForceCorrection_periodic
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) (hβs : tsupport β ⊆ Ioo (0 : ℝ) T)
    (lambda t : ℝ) :
    SpatialPeriodic ((localizedPairForce ν a β u F lambda - F) t) := by
  intro x j
  change localizedPairForce ν a β u F lambda t (x + unitVector j) - F t (x + unitVector j) =
    localizedPairForce ν a β u F lambda t x - F t x
  rw [(localizedPairForce_admissible h a hβ hβc hβs lambda).periodic t x j,
    h.force.periodic t x j]

end MethbokeAddon.FDSN
