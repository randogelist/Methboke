import MethbokeAddon.FDSN.FamilyContracts
import MethbokeAddon.FDSN.SmoothSmallness

/-!
# From actual derivative bounds to the literal FDSN C^r norm

The compact slab is nonempty, so its derivative suprema are not used through
an empty-set convention. A single finite-order bound controls their finite
sum. Applying the parameter mean-value theorem to the two jointly smooth
corrections supplies exactly the constants and radius in FDSN.5.
-/

set_option autoImplicit false

open Set SingularClosure
open scoped BigOperators ContDiff

namespace MethbokeAddon.FDSN

noncomputable section

theorem spacetimeCrNorm_le_of_derivative_bound
    (r : ℕ) (a b : ℝ) (hab : a ≤ b) (V : Velocity) (C : ℝ)
    (hbound : ∀ n : ℕ, n ≤ r → ∀ z ∈ Icc a b ×ˢ unitCube,
      ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => V y.1 y.2) z‖ ≤ C) :
    spacetimeCrNorm r a b V ≤ ((r + 1 : ℕ) : ℝ) * C := by
  have hK : (Icc a b ×ˢ unitCube).Nonempty := by
    refine ⟨(a, 0), ⟨le_rfl, hab⟩, ?_⟩
    simp [unitCube]
  unfold spacetimeCrNorm
  calc
    _ ≤ ∑ _n ∈ Finset.range (r + 1), C := by
      apply Finset.sum_le_sum
      intro n hn
      apply csSup_le (hK.image _)
      rintro y ⟨z, hz, rfl⟩
      exact hbound n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)) z hz
    _ = ((r + 1 : ℕ) : ℝ) * C := by simp

set_option maxHeartbeats 800000 in
theorem smooth_family_spacetimeCrNorm_linear_bound
    (G : ℝ × (ℝ × Vec) → Vec) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ z : ℝ × Vec, G (0, z) = 0)
    (a b : ℝ) (hab : a ≤ b) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lambda : ℝ, ‖lambda‖ ≤ 1 →
      spacetimeCrNorm r a b (fun t x => G (lambda, (t, x))) ≤ C * ‖lambda‖ := by
  have hK : IsCompact (Icc a b ×ˢ unitCube) :=
    isCompact_Icc.prod isCompact_unitCube
  obtain ⟨C, hC, hb⟩ := smooth_family_finite_order_linear_bound
    (E := ℝ × Vec) (F := Vec) G hG hzero (Icc a b ×ˢ unitCube) hK r
  refine ⟨((r + 1 : ℕ) : ℝ) * C, mul_nonneg (by positivity) hC, ?_⟩
  intro lambda hlambda
  have hsliceEq :
      (fun y : ℝ × Vec => (fun t x => G (lambda, (t, x))) y.1 y.2) =
        (fun y : ℝ × Vec => G (lambda, y)) := by
    funext y
    rcases y with ⟨t, x⟩
    rfl
  have hslice : ∀ n : ℕ, n ≤ r → ∀ z ∈ Icc a b ×ˢ unitCube,
      ‖iteratedFDeriv ℝ n
        (fun y : ℝ × Vec => (fun t x => G (lambda, (t, x))) y.1 y.2) z‖ ≤
          C * ‖lambda‖ := by
    intro n hn z hz
    rw [hsliceEq]
    exact hb lambda hlambda n hn z hz
  have hnorm := spacetimeCrNorm_le_of_derivative_bound r a b hab
    (fun t x => G (lambda, (t, x))) (C * ‖lambda‖) hslice
  calc
    _ ≤ ((r + 1 : ℕ) : ℝ) * (C * ‖lambda‖) :=
      hnorm
    _ = (((r + 1 : ℕ) : ℝ) * C) * ‖lambda‖ := by ring

/-- The literal C^r clause follows from global joint smoothness and vanishing
of both actual corrections at parameter zero. The radius is the explicit 1;
the constant depends on the chosen derivative order. -/
theorem smooth_corrections_imply_smallness
    (a b ε : ℝ) (hab : a ≤ b) (u F : Velocity) (U G : ℝ → Velocity)
    (hU : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      (U q.1 - u) q.2.1 q.2.2))
    (hG : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      (G q.1 - F) q.2.1 q.2.2))
    (hU0 : U 0 = u) (hG0 : G 0 = F) :
    SmoothSmallness a b ε u F U G := by
  intro r
  obtain ⟨C₁, hC₁, hb₁⟩ := smooth_family_spacetimeCrNorm_linear_bound
    (fun q : ℝ × (ℝ × Vec) => (U q.1 - u) q.2.1 q.2.2)
    hU (by intro z; simp only [hU0, sub_self, Pi.zero_apply]) a b hab r
  obtain ⟨C₂, hC₂, hb₂⟩ := smooth_family_spacetimeCrNorm_linear_bound
    (fun q : ℝ × (ℝ × Vec) => (G q.1 - F) q.2.1 q.2.2)
    hG (by intro z; simp only [hG0, sub_self, Pi.zero_apply]) a b hab r
  refine ⟨C₁ + C₂, 1, add_nonneg hC₁ hC₂, zero_lt_one, ?_⟩
  intro lambda hlambda
  have hlambda1 : ‖lambda‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact (lt_of_lt_of_le hlambda (min_le_right ε 1)).le
  have hb := add_le_add (hb₁ lambda hlambda1) (hb₂ lambda hlambda1)
  simpa only [Real.norm_eq_abs, add_mul] using hb

end

end MethbokeAddon.FDSN
