import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Linarith

/-!
# Order equivalences for reciprocal thresholds

All statements are scalar algebra on nonnegative enstrophy values. No time
evolution or PDE premise occurs here.
-/

set_option autoImplicit false

namespace MethbokeAddon.EhrenfestObstruction

theorem scalar_reciprocal_denominator_pos
    (eStar e : ℝ) (heStar : 0 < eStar) (he : 0 ≤ e) :
    0 < 1 + e / eStar := by
  have hdiv : 0 ≤ e / eStar := div_nonneg he heStar.le
  linarith

theorem reciprocal_threshold_pos
    (eStar R : ℝ) (heStar : 0 < eStar) (hR : 0 ≤ R) :
    0 < (1 + R / eStar)⁻¹ :=
  inv_pos.mpr (scalar_reciprocal_denominator_pos eStar R heStar hR)

/-- Being below an enstrophy threshold is equivalent to being strictly above
the corresponding reciprocal threshold. -/
theorem reciprocal_threshold_strict_iff
    (eStar e R : ℝ) (heStar : 0 < eStar) (he : 0 ≤ e) (hR : 0 ≤ R) :
    (1 + R / eStar)⁻¹ < (1 + e / eStar)⁻¹ ↔ e < R := by
  rw [inv_lt_inv₀
    (scalar_reciprocal_denominator_pos eStar R heStar hR)
    (scalar_reciprocal_denominator_pos eStar e heStar he)]
  constructor
  · intro h
    have hdiv : e / eStar < R / eStar := by linarith
    exact (div_lt_div_iff_of_pos_right heStar).mp hdiv
  · intro h
    have hdiv := div_lt_div_of_pos_right h heStar
    linarith

/-- A reciprocal value below the reciprocal threshold means the enstrophy
has reached or exceeded the original threshold. -/
theorem reciprocal_threshold_weak_iff
    (eStar e R : ℝ) (heStar : 0 < eStar) (he : 0 ≤ e) (hR : 0 ≤ R) :
    (1 + e / eStar)⁻¹ ≤ (1 + R / eStar)⁻¹ ↔ R ≤ e := by
  rw [inv_le_inv₀
    (scalar_reciprocal_denominator_pos eStar e heStar he)
    (scalar_reciprocal_denominator_pos eStar R heStar hR)]
  constructor
  · intro h
    have hdiv : R / eStar ≤ e / eStar := by linarith
    exact (div_le_div_iff_of_pos_right heStar).mp hdiv
  · intro h
    have hdiv := (div_le_div_iff_of_pos_right heStar).mpr h
    linarith

theorem reciprocal_threshold_eq_iff
    (eStar e R : ℝ) (heStar : 0 < eStar) (he : 0 ≤ e) (hR : 0 ≤ R) :
    (1 + e / eStar)⁻¹ = (1 + R / eStar)⁻¹ ↔ e = R := by
  constructor
  · intro h
    apply le_antisymm
    · exact (reciprocal_threshold_weak_iff eStar R e heStar hR he).mp h.ge
    · exact (reciprocal_threshold_weak_iff eStar e R heStar he hR).mp h.le
  · intro h
    rw [h]

end MethbokeAddon.EhrenfestObstruction

