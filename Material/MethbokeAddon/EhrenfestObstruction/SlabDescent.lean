import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith

/-!
# Scalar descent on a closed time slab

The comparison uses the explicit derivative rate and differentiability only
in the interior. No stopping condition or Navier--Stokes hypothesis occurs
in this scalar module.
-/

namespace MethbokeAddon.EhrenfestObstruction

open Set

/-- An upper bound on the explicit interior derivative gives terminal descent. -/
theorem terminal_le_of_rate_le
    (v rate : ℝ → ℝ) (T gamma : ℝ)
    (hT : 0 < T)
    (hcont : ContinuousOn v (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt v (rate t) t)
    (hrate : ∀ t ∈ Ioo 0 T, rate t ≤ -gamma) :
    v T ≤ v 0 - gamma * T := by
  obtain ⟨s, hs, hslope⟩ :=
    exists_hasDerivAt_eq_slope v rate hT hcont hderiv
  have hrate_s := hrate s hs
  rw [hslope] at hrate_s
  have hslope_le : (v T - v 0) / T ≤ -gamma := by
    simpa only [sub_zero] using hrate_s
  have hdiff : v T - v 0 ≤ -gamma * T :=
    (div_le_iff₀ hT).mp hslope_le
  linarith

/-- Terminal positivity is incompatible with descent consuming the initial budget. -/
theorem positive_terminal_contradiction
    (v rate : ℝ → ℝ) (T gamma : ℝ)
    (hT : 0 < T)
    (hcont : ContinuousOn v (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt v (rate t) t)
    (hrate : ∀ t ∈ Ioo 0 T, rate t ≤ -gamma)
    (hbudget : v 0 ≤ gamma * T)
    (hpositive : 0 < v T) : False := by
  have hterminal :=
    terminal_le_of_rate_le v rate T gamma hT hcont hderiv hrate
  linarith

end MethbokeAddon.EhrenfestObstruction

