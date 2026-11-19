import MethbokeAddon.EhrenfestObstruction.FourierL1
import SingularClosure.HighOrderEstimate
import SingularClosure.PhysicalProjection

/-!
# Support-independent component C1 bounds for finite Fourier synthesis

Source-prepared candidates; matching external cached compilation remains required.
The derivative operator is the actual Fourier multiplier, and the derivative
identity below is the existing physical Frechet derivative identity.
-/

set_option autoImplicit false

open SingularClosure
open scoped BigOperators

namespace MethbokeAddon.EhrenfestObstruction
noncomputable section

/-- One coordinate derivative consumes one actual Fourier Sobolev order. -/
theorem ehrenfest_coordinateDerivative_multiplier_bound
    (s : ℕ) (j : Fin 3) (k : Frequency) :
    torusSobolevWeight k ^ s * ‖derivativeSymbol j k‖ ≤
      1 * torusSobolevWeight k ^ (s + 1) := by
  rw [one_mul, pow_succ]
  exact mul_le_mul_of_nonneg_left (derivativeSymbol_norm_le_weight k j)
    (pow_nonneg (torusSobolevWeight_pos k).le s)

/-- The actual derivative multiplier as a continuous linear map. -/
def ehrenfestTorusSobolevCoordinateDerivative (s : ℕ) (j : Fin 3) :
    TorusSobolev (s + 1) →L[ℂ] TorusSobolev s :=
  torusSobolevMultiplier s (s + 1) (derivativeSymbol j) 1 zero_le_one
    (ehrenfest_coordinateDerivative_multiplier_bound s j)

@[simp]
theorem ehrenfestTorusSobolevCoordinateDerivative_coeff
    (s : ℕ) (j : Fin 3) (c : TorusSobolev (s + 1)) :
    (ehrenfestTorusSobolevCoordinateDerivative s j c).val =
      spectralMultiplier (derivativeSymbol j) c.val :=
  torusSobolevMultiplier_coeff s (s + 1) (derivativeSymbol j) 1 zero_le_one
    (ehrenfest_coordinateDerivative_multiplier_bound s j) c

theorem ehrenfestTorusSobolevCoordinateDerivative_norm_le
    (s : ℕ) (j : Fin 3) (c : TorusSobolev (s + 1)) :
    ‖ehrenfestTorusSobolevCoordinateDerivative s j c‖ ≤ ‖c‖ := by
  have heq : ehrenfestTorusSobolevCoordinateDerivative s j c =
      torusSobolevMultiplierLinear s (s + 1) (derivativeSymbol j) 1 zero_le_one
        (ehrenfest_coordinateDerivative_multiplier_bound s j) c :=
    (torusSobolevMultiplierLinear s (s + 1) (derivativeSymbol j) 1 zero_le_one
      (ehrenfest_coordinateDerivative_multiplier_bound s j)).mkContinuous_apply 1
      (torusSobolevMultiplierLinear_norm_le s (s + 1) (derivativeSymbol j) 1 zero_le_one
        (ehrenfest_coordinateDerivative_multiplier_bound s j)) c
  rw [heq]
  simpa only [one_mul] using
    torusSobolevMultiplierLinear_norm_le s (s + 1) (derivativeSymbol j) 1 zero_le_one
      (ehrenfest_coordinateDerivative_multiplier_bound s j) c

/-- Every projected velocity component is bounded uniformly in the cutoff. -/
theorem finiteSynthesis_component_abs_le_H3_norm
    (N : ℕ) (c : TorusSobolev 3) (x : Vec) (i : Fin 3) :
    |finiteSynthesis N c.val x i| ≤ Real.sqrt latticeSobolevConstant * ‖c‖ := by
  have h := finiteSynthesis_component_abs_le_H2_norm N
    (torusSobolevInclusionLinear 2 c) x i
  have hnorm := mul_le_mul_of_nonneg_left (torusSobolevInclusion_norm_le 2 c)
    (Real.sqrt_nonneg latticeSobolevConstant)
  simpa only [torusSobolevInclusionLinear_coeff] using h.trans hnorm

/-- Every projected coordinate-derivative component has the same uniform H3 bound. -/
theorem finiteSynthesis_coordinateDerivative_component_abs_le_H3_norm
    (N : ℕ) (c : TorusSobolev 3) (x : Vec) (j i : Fin 3) :
    |coordinateDerivative (finiteSynthesis N c.val) j x i| ≤
      Real.sqrt latticeSobolevConstant * ‖c‖ := by
  rw [finiteSynthesis_coordinateDerivative,
    ← ehrenfestTorusSobolevCoordinateDerivative_coeff 2 j c]
  exact (finiteSynthesis_component_abs_le_H2_norm N
    (ehrenfestTorusSobolevCoordinateDerivative 2 j c) x i).trans
    (mul_le_mul_of_nonneg_left
      (ehrenfestTorusSobolevCoordinateDerivative_norm_le 2 j c)
      (Real.sqrt_nonneg latticeSobolevConstant))

/-- Componentwise C1 control for the actual finite physical Fourier field. -/
theorem finiteSynthesis_C1_components_le_H3_norm
    (N : ℕ) (c : TorusSobolev 3) (x : Vec) :
    (∀ i : Fin 3, |finiteSynthesis N c.val x i| ≤
      Real.sqrt latticeSobolevConstant * ‖c‖) ∧
    (∀ j i : Fin 3, |coordinateDerivative (finiteSynthesis N c.val) j x i| ≤
      Real.sqrt latticeSobolevConstant * ‖c‖) :=
  ⟨fun i => finiteSynthesis_component_abs_le_H3_norm N c x i,
    fun j i => finiteSynthesis_coordinateDerivative_component_abs_le_H3_norm N c x j i⟩

end
end MethbokeAddon.EhrenfestObstruction
