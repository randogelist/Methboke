import MethbokeAddon.WeakFouriermanB.PhysicalBudgetContinuation
import MethbokeAddon.WeakFouriermanB.StrongContinuation

/-!
The maximal lifetime extends strictly beyond the prescribed finite cutoff.
If the maximal lifetime were at or before that cutoff, the derived H1 bound
would cover its whole pre-endpoint trajectory. Actual H1-controlled restart
and maximality would then force an infinite lifetime, contradicting the
finite cutoff. This includes equality without evaluating the trajectory at
its maximal endpoint.

The full open Fourier-budget hypothesis is retained. Prepared source only;
matching external cached compilation and fresh audits remain required.
No local Lean, Lake, kernel audit or project test was executed.
-/

set_option autoImplicit false

open Set SingularClosure
open scoped ENNReal

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- A finite full Fourier budget excludes both an earlier maximal endpoint
and an endpoint exactly equal to the prescribed cutoff.
-/
theorem maximal_classical_lifetime_strictly_exceeds_cutoff
    (ν cutoff : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (H : MaximalClassicalFront ν a u p Tmax)
    (hbudget : MaximalFourierBudgetFinite u Tmax cutoff) :
    ENNReal.ofReal cutoff < Tmax := by
  by_contra hnot
  have hle : Tmax ≤ ENNReal.ofReal cutoff := le_of_not_gt hnot
  obtain ⟨R, _, hR⟩ := maximal_front_uniform_H1_before_budget_cap
    ν cutoff a u p Tmax hν H hbudget
  have htop : Tmax = ⊤ := maximal_classical_lifetime_eq_top_of_uniform_H1
    ν R a u p Tmax hν H (by
      intro t ht htmax
      exact hR t ht (by simpa only [min_eq_left hle] using htmax))
  exact (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle) htop

/-- Strict cutoff overlap gives a genuine positive classical front with
duration beyond that cutoff, suitable for the finite-cap admission theorem.
-/
theorem maximal_front_exists_strictly_after_cutoff
    (ν cutoff : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (hcutoff : 0 ≤ cutoff)
    (H : MaximalClassicalFront ν a u p Tmax)
    (hbudget : MaximalFourierBudgetFinite u Tmax cutoff) :
    ∃ T : ℝ, 0 < T ∧ cutoff < T ∧ ENNReal.ofReal T < Tmax ∧
      InitialClassicalFront ν T a u p := by
  have hstrict := maximal_classical_lifetime_strictly_exceeds_cutoff
    ν cutoff a u p Tmax hν H hbudget
  obtain ⟨T, hT0, hcutT, hTmax⟩ := ENNReal.lt_iff_exists_real_btwn.mp hstrict
  have hcut : cutoff < T :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hcutoff).mp hcutT
  have hT : 0 < T := hcutoff.trans_lt hcut
  exact ⟨T, hT, hcut, hTmax, H.finite_front T hT hTmax⟩

end
end MethbokeAddon.WeakFouriermanB
