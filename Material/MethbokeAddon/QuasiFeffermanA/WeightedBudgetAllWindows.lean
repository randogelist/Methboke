import MethbokeAddon.QuasiFeffermanA.Energy

/-!
# Physical Leray--Hopf weighted budget on every nonnegative finite window

The accepted positive-horizon energy--enstrophy product theorem is extended
to the zero-length window. The statement uses the actual full-volume L2
velocity and three weak spatial derivatives. It supplies integrability and
the exact one-quarter bound for every real T >= 0.

The zero case is the empty open interval; no existence, regularity,
comparison, continuation, or product-integrability premise is added.
Global existence of a Leray--Hopf path remains a separate construction.

Prepared for matching external compilation
and independent literal type/axiom audit. No local Lean execution is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace MethbokeAddon.QuasiFeffermanA

/-- The actual energy--enstrophy product is integrable on every finite
nonnegative horizon, with the unchanged factor-one-quarter budget. -/
theorem LerayHopf.energy_product_budget_Ioo_nonneg
    {ν T : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 < ν) (hT : 0 ≤ T) :
    Integrable (fun t => ‖u t‖ ^ 2 * (∑ j : Fin 3, ‖G t j‖ ^ 2))
        (volume.restrict (Ioo (0 : ℝ) T)) ∧
      (∫ t in Ioo (0 : ℝ) T, ‖u t‖ ^ 2 * (∑ j : Fin 3, ‖G t j‖ ^ 2)) ≤
        ‖a‖ ^ 4 / (4 * ν) := by
  rcases eq_or_lt_of_le hT with hT | hT
  · subst T
    constructor
    · rw [Ioo_self, Measure.restrict_empty]
      exact integrable_zero_measure
    · rw [Ioo_self, Measure.restrict_empty, integral_zero_measure]
      exact div_nonneg (pow_nonneg (norm_nonneg a) 4)
        (mul_nonneg (by norm_num) hν.le)
  · exact h.energy_product_budget_Ioo hν hT

end MethbokeAddon.QuasiFeffermanA
