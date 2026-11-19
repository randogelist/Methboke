import SingularClosure.LatticeSobolevSummability
import SingularClosure.FourierSobolevOperators
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Finite Fourier component bounds from the actual H2 norm

These are source-prepared candidates for the Ehrenfest smooth-reference layer.
They use the actual weighted coefficient space and actual finite synthesis.
No solution, convergence, residual-bound or regularity port is assumed.
Matching external cached compilation and fresh type/axiom audits are required.
No local Lean execution was used.
-/

set_option autoImplicit false

open SingularClosure
open scoped BigOperators

namespace MethbokeAddon.EhrenfestObstruction
noncomputable section

/-- A single component's finite H2 sum is bounded by the full H2 norm. -/
theorem finite_component_H2_sum_le (s : Finset Frequency)
    (c : TorusSobolev 2) (i : Fin 3) :
    (∑ k ∈ s, (torusSobolevWeight k ^ 2 * ‖c.val k i‖) ^ 2) ≤ ‖c‖ ^ 2 := by
  have h := torusSobolev_finite_weighted_sum_le 2 c
    (s.product ({i} : Finset (Fin 3)))
  have hproduct :
      (∑ ki ∈ s.product ({i} : Finset (Fin 3)),
        ‖sobolevWeightedCoeff 2 c.val ki‖ ^ 2) =
      ∑ k ∈ s, ∑ j ∈ ({i} : Finset (Fin 3)),
        ‖sobolevWeightedCoeff 2 c.val (k, j)‖ ^ 2 :=
    Finset.sum_product s ({i} : Finset (Fin 3))
      (fun ki : FourierIndex => ‖sobolevWeightedCoeff 2 c.val ki‖ ^ 2)
  rw [hproduct] at h
  simpa only [Finset.sum_singleton, torusSobolev_weightedCoeff_norm] using h

/-- The finite coefficient l1 square has a support-independent H2 bound. -/
theorem finite_component_l1_sq_le_H2_norm_sq (s : Finset Frequency)
    (c : TorusSobolev 2) (i : Fin 3) :
    (∑ k ∈ s, ‖c.val k i‖) ^ 2 ≤ latticeSobolevConstant * ‖c‖ ^ 2 := by
  exact (finite_l1_sq_le_H2_sq s (fun k => c.val k i)).trans
    (mul_le_mul_of_nonneg_left (finite_component_H2_sum_le s c i)
      latticeSobolevConstant_pos.le)

/-- A support-independent scalar Fourier l1 bound with an explicit constant. -/
theorem finite_component_l1_le_H2_norm (s : Finset Frequency)
    (c : TorusSobolev 2) (i : Fin 3) :
    (∑ k ∈ s, ‖c.val k i‖) ≤ Real.sqrt latticeSobolevConstant * ‖c‖ := by
  have hsq := finite_component_l1_sq_le_H2_norm_sq s c i
  have hsum : 0 ≤ ∑ k ∈ s, ‖c.val k i‖ :=
    Finset.sum_nonneg (fun k _ => norm_nonneg _)
  have hright : 0 ≤ Real.sqrt latticeSobolevConstant * ‖c‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hright_sq : (Real.sqrt latticeSobolevConstant * ‖c‖) ^ 2 =
      latticeSobolevConstant * ‖c‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt latticeSobolevConstant_pos.le]
  exact (sq_le_sq₀ hsum hright).mp (hsq.trans_eq hright_sq.symm)

/-- The actual unit-period Fourier characters have unit complex norm. -/
theorem ehrenfest_fourierCharacter_norm (k : Frequency) (x : Vec) :
    ‖fourierCharacter k x‖ = 1 := by
  simp [fourierCharacter, Complex.norm_exp, Complex.mul_re]

/-- Every finite-synthesis component is bounded by its coefficient l1 sum. -/
theorem finiteSynthesis_component_abs_le_l1
    (N : ℕ) (c : FourierCoeff) (x : Vec) (i : Fin 3) :
    |finiteSynthesis N c x i| ≤ ∑ k ∈ cutoffModes N, ‖c k i‖ := by
  change |(∑ k ∈ cutoffModes N, fourierCharacter k x * c k i).re| ≤ _
  calc
    _ ≤ ‖∑ k ∈ cutoffModes N, fourierCharacter k x * c k i‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑ k ∈ cutoffModes N, ‖fourierCharacter k x * c k i‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ cutoffModes N, ‖c k i‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul, ehrenfest_fourierCharacter_norm, one_mul]

/-- Uniform pointwise component control of the actual finite real synthesis. -/
theorem finiteSynthesis_component_abs_le_H2_norm
    (N : ℕ) (c : TorusSobolev 2) (x : Vec) (i : Fin 3) :
    |finiteSynthesis N c.val x i| ≤ Real.sqrt latticeSobolevConstant * ‖c‖ :=
  (finiteSynthesis_component_abs_le_l1 N c.val x i).trans
    (finite_component_l1_le_H2_norm (cutoffModes N) c i)

end
end MethbokeAddon.EhrenfestObstruction
