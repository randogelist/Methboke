import EhrenfestScalar.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-!
Exact, independently written consumer propositions for external verification.
This file is a candidate and has not been executed locally.
-/

open Set MethbokeAddon.EhrenfestObstruction

namespace EhrenfestScalar.TypeChecks

example :
    ∀ (v rate : ℝ → ℝ) (T gamma : ℝ),
      0 < T →
      ContinuousOn v (Icc 0 T) →
      (∀ t ∈ Ioo 0 T, HasDerivAt v (rate t) t) →
      (∀ t ∈ Ioo 0 T, rate t ≤ -gamma) →
      v T ≤ v 0 - gamma * T :=
  @MethbokeAddon.EhrenfestObstruction.terminal_le_of_rate_le

example :
    ∀ (v rate : ℝ → ℝ) (T gamma : ℝ),
      0 < T →
      ContinuousOn v (Icc 0 T) →
      (∀ t ∈ Ioo 0 T, HasDerivAt v (rate t) t) →
      (∀ t ∈ Ioo 0 T, rate t ≤ -gamma) →
      v 0 ≤ gamma * T →
      0 < v T →
      False :=
  @MethbokeAddon.EhrenfestObstruction.positive_terminal_contradiction

example :
    ∀ (v rate : ℝ → ℝ) (gamma r : ℝ),
      0 < gamma → 0 < r → r < v 0 → v 0 ≤ 1 →
      ContinuousOn v (Icc 0 (1 / gamma)) →
      (∀ t, 0 ≤ t → t < 1 / gamma →
        (∀ s, 0 ≤ s → s ≤ t → r < v s) →
        HasDerivWithinAt v (rate t) (Ici 0) t ∧ rate t ≤ -gamma) →
      ∃ t ∈ Icc 0 ((v 0 - r) / gamma), v t ≤ r :=
  @MethbokeAddon.EhrenfestObstruction.stopped_scalar_le_by_deadline

example :
    ∀ (v rate : ℝ → ℝ) (gamma r : ℝ),
      0 < gamma → 0 < r → r < v 0 → v 0 ≤ 1 →
      ContinuousOn v (Icc 0 (1 / gamma)) →
      (∀ t, 0 ≤ t → t < 1 / gamma →
        (∀ s, 0 ≤ s → s ≤ t → r < v s) →
        HasDerivWithinAt v (rate t) (Ici 0) t ∧ rate t ≤ -gamma) →
      ∃ t ∈ Icc 0 ((v 0 - r) / gamma), v t = r :=
  @MethbokeAddon.EhrenfestObstruction.stopped_scalar_hitting

end EhrenfestScalar.TypeChecks


#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.terminal_le_of_rate_le"
#check @MethbokeAddon.EhrenfestObstruction.terminal_le_of_rate_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.terminal_le_of_rate_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.terminal_le_of_rate_le"
#print axioms MethbokeAddon.EhrenfestObstruction.terminal_le_of_rate_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.terminal_le_of_rate_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.positive_terminal_contradiction"
#check @MethbokeAddon.EhrenfestObstruction.positive_terminal_contradiction
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.positive_terminal_contradiction"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.positive_terminal_contradiction"
#print axioms MethbokeAddon.EhrenfestObstruction.positive_terminal_contradiction
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.positive_terminal_contradiction"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_scalar_le_by_deadline"
#check @MethbokeAddon.EhrenfestObstruction.stopped_scalar_le_by_deadline
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.stopped_scalar_le_by_deadline"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_scalar_le_by_deadline"
#print axioms MethbokeAddon.EhrenfestObstruction.stopped_scalar_le_by_deadline
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.stopped_scalar_le_by_deadline"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_scalar_hitting"
#check @MethbokeAddon.EhrenfestObstruction.stopped_scalar_hitting
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.stopped_scalar_hitting"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_scalar_hitting"
#print axioms MethbokeAddon.EhrenfestObstruction.stopped_scalar_hitting
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.stopped_scalar_hitting"

