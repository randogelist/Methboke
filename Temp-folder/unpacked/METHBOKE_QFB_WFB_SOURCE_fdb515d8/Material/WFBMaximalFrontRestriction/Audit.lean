import WFBMaximalFrontRestriction.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter SingularClosure
open scoped ContDiff ENNReal Topology
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.maximal_classical_front_restrict_le
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (H : MaximalClassicalFront ν a u p Tmax) (hT : 0 < T)
    (hTmax : ENNReal.ofReal T ≤ Tmax),
    InitialClassicalFront ν T a u p :=
  @MethbokeAddon.WeakFouriermanB.maximal_classical_front_restrict_le

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_front_restrict_le"
#check @MethbokeAddon.WeakFouriermanB.maximal_classical_front_restrict_le
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.maximal_classical_front_restrict_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_front_restrict_le"
#print axioms MethbokeAddon.WeakFouriermanB.maximal_classical_front_restrict_le
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.maximal_classical_front_restrict_le"
