import SingularClosure.SixChannels

/-!
# A conjugate Fourier-pair rotation for the periodic FDSN construction

These are actual coefficient operations on `Frequency = Fin 3 → ℤ`.
The zero mode is retained.  Physical Fourier reconstruction and the
time-dependent NSE realization are separate later endpoints.

Prepared by static source inspection for external CI only.
-/

set_option autoImplicit false

open scoped BigOperators

namespace MethbokeAddon.FDSN

open SingularClosure

noncomputable section

/-- Multiply one chosen mode by `z`, its opposite by `star z`, and retain
every other mode.  The nonzero-mode condition is imposed on the theorems. -/
def pairMultiplier (a : Frequency) (z : ℂ) (k : Frequency) : ℂ :=
  if k = a then z else if k = -a then star z else 1

def pairRotate (a : Frequency) (z : ℂ) (c : FourierCoeff) : FourierCoeff :=
  fun k i => pairMultiplier a z k * c k i

theorem frequency_ne_neg_self {a : Frequency} (ha : a ≠ 0) : a ≠ -a := by
  intro h
  apply ha
  funext i
  have hi := congrFun h i
  simp only [Pi.neg_apply] at hi
  change a i = 0
  omega

@[simp]
theorem pairMultiplier_at (a : Frequency) (z : ℂ) :
    pairMultiplier a z a = z := by
  simp [pairMultiplier]

theorem pairMultiplier_at_neg {a : Frequency} (ha : a ≠ 0) (z : ℂ) :
    pairMultiplier a z (-a) = star z := by
  simp [pairMultiplier, Ne.symm (frequency_ne_neg_self ha)]

theorem pairMultiplier_off {a k : Frequency} (z : ℂ)
    (hka : k ≠ a) (hkna : k ≠ -a) : pairMultiplier a z k = 1 := by
  simp [pairMultiplier, hka, hkna]

theorem pairMultiplier_at_zero {a : Frequency} (ha : a ≠ 0) (z : ℂ) :
    pairMultiplier a z 0 = 1 := by
  have hna : (0 : Frequency) ≠ -a := by
    intro h
    apply ha
    have hh := congrArg Neg.neg h
    simpa using hh.symm
  exact pairMultiplier_off z (Ne.symm ha) hna

theorem pairMultiplier_neg {a : Frequency} (ha : a ≠ 0)
    (z : ℂ) (k : Frequency) :
    pairMultiplier a z (-k) = star (pairMultiplier a z k) := by
  classical
  by_cases hk : k = a
  · subst k
    rw [pairMultiplier_at_neg ha, pairMultiplier_at]
  · by_cases hkn : k = -a
    · subst k
      simp only [neg_neg, pairMultiplier_at, pairMultiplier_at_neg ha, star_star]
    · have hnka : -k ≠ a := by
        intro h
        apply hkn
        have hh := congrArg Neg.neg h
        simpa using hh
      have hnkna : -k ≠ -a := by
        intro h
        apply hk
        exact neg_injective h
      simp [pairMultiplier, hk, hkn, hnka, hnkna]

theorem pairMultiplier_norm (a : Frequency) {z : ℂ} (hz : ‖z‖ = 1)
    (k : Frequency) : ‖pairMultiplier a z k‖ = 1 := by
  classical
  unfold pairMultiplier
  split_ifs <;> simp_all

@[simp]
theorem pairMultiplier_one (a k : Frequency) : pairMultiplier a 1 k = 1 := by
  classical
  simp [pairMultiplier]

@[simp]
theorem pairRotate_one (a : Frequency) (c : FourierCoeff) :
    pairRotate a 1 c = c := by
  funext k i
  simp [pairRotate]

theorem pairRotate_at (a : Frequency) (z : ℂ) (c : FourierCoeff) :
    pairRotate a z c a = z • c a := by
  funext i
  simp [pairRotate]

theorem pairRotate_at_neg {a : Frequency} (ha : a ≠ 0)
    (z : ℂ) (c : FourierCoeff) :
    pairRotate a z c (-a) = star z • c (-a) := by
  funext i
  simp [pairRotate, pairMultiplier_at_neg ha]

theorem pairRotate_off {a k : Frequency} (z : ℂ) (c : FourierCoeff)
    (hka : k ≠ a) (hkna : k ≠ -a) : pairRotate a z c k = c k := by
  funext i
  simp [pairRotate, pairMultiplier_off z hka hkna]

theorem pairRotate_mean {a : Frequency} (ha : a ≠ 0)
    (z : ℂ) (c : FourierCoeff) : pairRotate a z c 0 = c 0 := by
  funext i
  simp [pairRotate, pairMultiplier_at_zero ha]

theorem pairRotate_reality {a : Frequency} (ha : a ≠ 0)
    (z : ℂ) {c : FourierCoeff} (hc : SpectralReality c) :
    SpectralReality (pairRotate a z c) := by
  intro k i
  change pairMultiplier a z (-k) * c (-k) i = star (pairMultiplier a z k * c k i)
  rw [pairMultiplier_neg ha, hc k i, star_mul]
  ring

theorem pairRotate_solenoidal (a : Frequency) (z : ℂ)
    {c : FourierCoeff} (hc : SpectralSolenoidal c) :
    SpectralSolenoidal (pairRotate a z c) := by
  intro k
  change (∑ i : Fin 3, (k i : ℂ) * (pairMultiplier a z k * c k i)) = 0
  calc
    _ = pairMultiplier a z k * ∑ i : Fin 3, (k i : ℂ) * c k i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [hc k, mul_zero]

theorem pairRotate_component_norm (a : Frequency) {z : ℂ} (hz : ‖z‖ = 1)
    (c : FourierCoeff) (k : Frequency) (i : Fin 3) :
    ‖pairRotate a z c k i‖ = ‖c k i‖ := by
  simp only [pairRotate, norm_mul, pairMultiplier_norm a hz, one_mul]

/-- A common scalar phase preserves any complex-linear modal observation.
In particular this applies to each helical coordinate once its concrete
linear functional has been defined. -/
theorem pairRotate_observable_norm (a : Frequency) {z : ℂ} (hz : ‖z‖ = 1)
    (c : FourierCoeff) (k : Frequency) (L : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) :
    ‖L (pairRotate a z c k)‖ = ‖L (c k)‖ := by
  have h : L (pairRotate a z c k) = pairMultiplier a z k * L (c k) := by
    change L (pairMultiplier a z k • c k) = _
    simpa only [smul_eq_mul] using L.map_smul (pairMultiplier a z k) (c k)
  rw [h, norm_mul, pairMultiplier_norm a hz, one_mul]

/-- Exact termwise preservation of weighted component powers.  Integrability
and the passage to physical Sobolev norms are proved in separate adapters. -/
theorem pairRotate_weighted_power_sum (a : Frequency) {z : ℂ} (hz : ‖z‖ = 1)
    (c : FourierCoeff) (w : Frequency → ℝ) :
    (∑' k : Frequency, w k * ∑ i : Fin 3, ‖pairRotate a z c k i‖ ^ 2) =
      ∑' k : Frequency, w k * ∑ i : Fin 3, ‖c k i‖ ^ 2 := by
  apply tsum_congr
  intro k
  simp only [pairRotate_component_norm a hz]

/-- Coefficient-level middle endpoint for the single-pair torus deformation.
This theorem constructs the rotation from the input coefficients; it does
not assume a family or a physical reconstruction theorem. -/
theorem PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_CONSTRAINTS
    {a : Frequency} (ha : a ≠ 0) {z : ℂ} (hz : ‖z‖ = 1)
    (c : FourierCoeff) (hr : SpectralReality c) (hs : SpectralSolenoidal c) :
    SpectralReality (pairRotate a z c) ∧
    SpectralSolenoidal (pairRotate a z c) ∧
    pairRotate a z c 0 = c 0 ∧
    (∀ k : Frequency, ∀ L : (Fin 3 → ℂ) →ₗ[ℂ] ℂ,
      ‖L (pairRotate a z c k)‖ = ‖L (c k)‖) := by
  exact ⟨pairRotate_reality ha z hr, pairRotate_solenoidal a z hs,
    pairRotate_mean ha z c, fun k L => pairRotate_observable_norm a hz c k L⟩

end

end MethbokeAddon.FDSN
