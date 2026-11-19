import SingularClosure.EnstrophyAbsorption

/-!
Finite-coefficient H1 calculus for forced errors.

The derivative theorem applies to arbitrary coordinatewise differentiable
curves. In particular, no `GalerkinSolution` instance is assigned to an error
curve. The forced balance assumes its literal coordinate equation, whose PDE
identification is a separate task.

Prepared source: external cached compiler and axiom audit are still required.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff RealInnerProductSpace

namespace MethbokeAddon.EhrenfestObstruction

noncomputable section

/-- Twice the real Fourier pairing with the positive Laplacian weight. -/
def dissipationRatePairing (N : ℕ) (c d : FourierCoeff) : ℝ :=
  ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
    ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) *
      (2 * (star (c k i) * d k i).re)

/-- The H1 square derivative needs only the actual coordinate derivatives. -/
theorem coefficient_dissipation_hasDerivWithinAt
    (N : ℕ) (c : ℝ → FourierCoeff) (d : FourierCoeff)
    {s : Set ℝ} {t : ℝ}
    (hc : ∀ k ∈ cutoffModes N, ∀ i : Fin 3,
      HasDerivWithinAt (fun r => c r k i) (d k i) s t) :
    HasDerivWithinAt (fun r => coefficientDissipation N (c r))
      (dissipationRatePairing N (c t) d) s t := by
  unfold coefficientDissipation dissipationRatePairing
  apply HasDerivWithinAt.fun_sum
  intro k hk
  apply HasDerivWithinAt.fun_sum
  intro i hi
  exact (hasDerivWithinAt_complex_normSq (hc k hk i)).const_mul _

/-- Subtraction preserves the exact finite-coefficient derivative formula. -/
theorem coefficient_error_dissipation_hasDerivWithinAt
    (N : ℕ) (c v : ℝ → FourierCoeff) (dc dv : FourierCoeff)
    {s : Set ℝ} {t : ℝ}
    (hc : ∀ k ∈ cutoffModes N, ∀ i : Fin 3,
      HasDerivWithinAt (fun r => c r k i) (dc k i) s t)
    (hv : ∀ k ∈ cutoffModes N, ∀ i : Fin 3,
      HasDerivWithinAt (fun r => v r k i) (dv k i) s t) :
    HasDerivWithinAt
      (fun r => coefficientDissipation N (c r - v r))
      (dissipationRatePairing N (c t - v t) (dc - dv)) s t := by
  apply coefficient_dissipation_hasDerivWithinAt
  intro k hk i
  exact (hc k hk i).sub (hv k hk i)

theorem dissipationRatePairing_add_right
    (N : ℕ) (c d f : FourierCoeff) :
    dissipationRatePairing N c (d + f) =
      dissipationRatePairing N c d + dissipationRatePairing N c f := by
  simp only [dissipationRatePairing, Pi.add_apply, mul_add,
    Complex.add_re, Finset.sum_add_distrib]

theorem dissipationRatePairing_sub_right
    (N : ℕ) (c d f : FourierCoeff) :
    dissipationRatePairing N c (d - f) =
      dissipationRatePairing N c d - dissipationRatePairing N c f := by
  simp only [dissipationRatePairing, Pi.sub_apply, mul_sub,
    Complex.sub_re, Finset.sum_sub_distrib]

theorem dissipationRatePairing_galerkinRhs
    (ν : ℝ) (N : ℕ) (c : FourierCoeff) :
    dissipationRatePairing N c (galerkinRhs ν N c) =
      (-2 * ν) * coefficientLaplacianSquare N c -
        2 * coefficientEnstrophyNonlinearPower N c :=
  coefficientDissipation_rate_split ν N c

/-- Exact H1 balance for a forced finite equation, on any time set. -/
theorem forced_coefficient_dissipation_identity
    (ν : ℝ) (N : ℕ) (c : ℝ → FourierCoeff) (f : FourierCoeff)
    {s : Set ℝ} {t : ℝ}
    (heq : ∀ k ∈ cutoffModes N, ∀ i : Fin 3,
      HasDerivWithinAt (fun r => c r k i)
        (galerkinRhs ν N (c t) k i + f k i) s t) :
    HasDerivWithinAt (fun r => coefficientDissipation N (c r))
      ((-2 * ν) * coefficientLaplacianSquare N (c t) -
        2 * coefficientEnstrophyNonlinearPower N (c t) +
        dissipationRatePairing N (c t) f) s t := by
  have hd := coefficient_dissipation_hasDerivWithinAt N c
    (galerkinRhs ν N (c t) + f) heq
  rw [dissipationRatePairing_add_right,
    dissipationRatePairing_galerkinRhs] at hd
  exact hd

/-- Arbitrary finite real solenoidal fields obey the same self-interaction
absorption as Galerkin solutions. No evolution equation is used here. -/
theorem FINITE_ERROR_NONLINEAR_ABSORPTION :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ N : ℕ,
      ∀ c : FourierCoeff,
      (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0) →
      SpectralReality c → SpectralSolenoidal c →
      -2 * coefficientEnstrophyNonlinearPower N c ≤
        ν * coefficientLaplacianSquare N c +
          C / ν ^ 3 * (coefficientDissipation N c) ^ 3 := by
  obtain ⟨K, hK, hbound⟩ := FINITE_PHYSICAL_NONLINEAR_REAL_BOUND
  let C : ℝ := (2 * K) ^ 4 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ν hν N c hsupp hreal hsol
  have hE := coefficientDissipation_nonneg N c
  have hZ := coefficientLaplacianSquare_nonneg N c
  have hb := hbound N c hreal
  have ha := nonlinear_three_quarter_absorption hK hE hZ hν
  calc
    _ = 2 * (∫ x in unitCube,
        inner ℝ (convection (finiteSynthesis N c) x)
          (laplacian (finiteSynthesis N c) x)) := by
      rw [coefficientEnstrophyNonlinearPower_eq_physical N c hsupp hreal hsol]
      ring
    _ ≤ 2 * abs (∫ x in unitCube,
        inner ℝ (convection (finiteSynthesis N c) x)
          (laplacian (finiteSynthesis N c) x)) :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    _ ≤ 2 * (K * (coefficientDissipation N c) ^ (3 / 4 : ℝ) *
        (coefficientLaplacianSquare N c) ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = 2 * K * (coefficientDissipation N c) ^ (3 / 4 : ℝ) *
        (coefficientLaplacianSquare N c) ^ (3 / 4 : ℝ) := by ring
    _ ≤ ν * coefficientLaplacianSquare N c +
        (2 * K) ^ 4 / ν ^ 3 * (coefficientDissipation N c) ^ 3 := ha
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hE _)
      apply div_le_div_of_nonneg_right _ (pow_nonneg hν.le _)
      dsimp [C]
      linarith

/-- Uniform H1 inequality with the literal forcing power retained exactly.
The forcing can include cross transport and a projected-reference residual. -/
theorem FORCED_COEFFICIENT_ENSTROPHY_INEQUALITY :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ N : ℕ,
      ∀ c : ℝ → FourierCoeff, ∀ f : FourierCoeff,
      ∀ s : Set ℝ, ∀ t : ℝ,
      (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c t k i = 0) →
      SpectralReality (c t) → SpectralSolenoidal (c t) →
      (∀ k ∈ cutoffModes N, ∀ i : Fin 3,
        HasDerivWithinAt (fun r => c r k i)
          (galerkinRhs ν N (c t) k i + f k i) s t) →
      ∃ d : ℝ,
        HasDerivWithinAt (fun r => coefficientDissipation N (c r)) d s t ∧
        d + ν * coefficientLaplacianSquare N (c t) ≤
          C / ν ^ 3 * (coefficientDissipation N (c t)) ^ 3 +
            dissipationRatePairing N (c t) f := by
  obtain ⟨C, hC, hbound⟩ := FINITE_ERROR_NONLINEAR_ABSORPTION
  refine ⟨C, hC, ?_⟩
  intro ν hν N c f s t hsupp hreal hsol heq
  refine ⟨(-2 * ν) * coefficientLaplacianSquare N (c t) -
    2 * coefficientEnstrophyNonlinearPower N (c t) +
    dissipationRatePairing N (c t) f,
    forced_coefficient_dissipation_identity ν N c f heq, ?_⟩
  have h := hbound ν hν N (c t) hsupp hreal hsol
  linarith

end

end MethbokeAddon.EhrenfestObstruction
