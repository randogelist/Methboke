import MethbokeAddon.FDSN.LocalizedResidual
import MethbokeAddon.FDSN.SmoothSmallness

/-!
# Actual velocity and force corrections are small in every finite smooth norm

The common compact set may be the closed time slab times the periodic unit
cell. The derivatives are actual full time-space Fréchet derivatives of each
fixed-parameter correction.
-/

set_option autoImplicit false

noncomputable section

open Set SingularClosure
open scoped ContDiff

namespace MethbokeAddon.FDSN

theorem localizedPairVelocity_finite_order_linear_bound
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T)
    (K : Set (ℝ × Vec)) (hK : IsCompact K) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lambda : ℝ, ‖lambda‖ ≤ 1 →
      ∀ n : ℕ, n ≤ r → ∀ z ∈ K,
        ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec =>
          (localizedPairVelocity a β u lambda - u) y.1 y.2) z‖ ≤ C * ‖lambda‖ := by
  simp_rw [localizedPairVelocity_sub_eq_correction]
  apply smooth_family_finite_order_linear_bound
    (fun q : ℝ × (ℝ × Vec) => localizedPairCorrection a β u q.1 q.2.1 q.2.2)
    (localizedPairCorrection_joint_smooth h a hβ hβs) _ K hK r
  intro z
  rw [localizedPairCorrection_zero_parameter]
  rfl

theorem localizedPairForce_finite_order_linear_bound
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T)
    (K : Set (ℝ × Vec)) (hK : IsCompact K) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lambda : ℝ, ‖lambda‖ ≤ 1 →
      ∀ n : ℕ, n ≤ r → ∀ z ∈ K,
        ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec =>
          (localizedPairForce ν a β u F lambda - F) y.1 y.2) z‖ ≤ C * ‖lambda‖ := by
  apply smooth_family_finite_order_linear_bound
    (fun q : ℝ × (ℝ × Vec) => (localizedPairForce ν a β u F q.1 - F) q.2.1 q.2.2)
    (localizedPairForceCorrection_joint_smooth h a hβ hβs) _ K hK r
  intro z
  rw [localizedPairForce_zero_parameter, sub_self]
  rfl

end MethbokeAddon.FDSN
