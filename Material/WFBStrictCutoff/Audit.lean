import WFBStrictCutoff.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set SingularClosure
open scoped ENNReal
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_strictly_exceeds_cutoff
example : ∀ (ν cutoff : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (H : MaximalClassicalFront ν a u p Tmax)
    (hbudget : MaximalFourierBudgetFinite u Tmax cutoff),
    ENNReal.ofReal cutoff < Tmax :=
  @MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_strictly_exceeds_cutoff

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.maximal_front_exists_strictly_after_cutoff
example : ∀ (ν cutoff : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (hcutoff : 0 ≤ cutoff)
    (H : MaximalClassicalFront ν a u p Tmax)
    (hbudget : MaximalFourierBudgetFinite u Tmax cutoff),
    ∃ T : ℝ, 0 < T ∧ cutoff < T ∧ ENNReal.ofReal T < Tmax ∧
      InitialClassicalFront ν T a u p :=
  @MethbokeAddon.WeakFouriermanB.maximal_front_exists_strictly_after_cutoff

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_strictly_exceeds_cutoff"
#check @MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_strictly_exceeds_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_strictly_exceeds_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_strictly_exceeds_cutoff"
#print axioms MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_strictly_exceeds_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_strictly_exceeds_cutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_front_exists_strictly_after_cutoff"
#check @MethbokeAddon.WeakFouriermanB.maximal_front_exists_strictly_after_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.maximal_front_exists_strictly_after_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_front_exists_strictly_after_cutoff"
#print axioms MethbokeAddon.WeakFouriermanB.maximal_front_exists_strictly_after_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.maximal_front_exists_strictly_after_cutoff"
