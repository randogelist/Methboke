import WFBLocalClassicalUniqueness.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped ContDiff Topology
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_restrict
example : ∀ (ν T S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hST : S ≤ T),
    InitialClassicalFront ν S a u p :=
  @MethbokeAddon.WeakFouriermanB.initial_front_restrict

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.global_smooth_to_initial_front
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : GlobalSmoothNSE ν a u p),
    InitialClassicalFront ν T a u p :=
  @MethbokeAddon.WeakFouriermanB.global_smooth_to_initial_front

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_congr
example : ∀ (ν T : ℝ) (a : Field) (u v : Velocity) (p q : Pressure)
    (H : InitialClassicalFront ν T a u p) (hT : 0 < T)
    (huv : ∀ r ∈ Ico (0 : ℝ) T, v r = u r)
    (hpq : ∀ r ∈ Ico (0 : ℝ) T, q r = p r),
    InitialClassicalFront ν T a v q :=
  @MethbokeAddon.WeakFouriermanB.initial_front_congr

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_classical_front_unique
example : ∀ (ν T S : ℝ) (a : Field) (u v : Velocity) (p q : Pressure)
    (hν : 0 < ν) (hT : 0 < T) (hS : 0 < S)
    (H : InitialClassicalFront ν T a u p)
    (K : InitialClassicalFront ν S a v q),
    ∀ r ∈ Ico (0 : ℝ) (min T S), u r = v r ∧ p r = q r :=
  @MethbokeAddon.WeakFouriermanB.initial_classical_front_unique

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_restrict"
#check @MethbokeAddon.WeakFouriermanB.initial_front_restrict
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_restrict"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_restrict"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_restrict
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_restrict"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.global_smooth_to_initial_front"
#check @MethbokeAddon.WeakFouriermanB.global_smooth_to_initial_front
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.global_smooth_to_initial_front"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.global_smooth_to_initial_front"
#print axioms MethbokeAddon.WeakFouriermanB.global_smooth_to_initial_front
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.global_smooth_to_initial_front"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_congr"
#check @MethbokeAddon.WeakFouriermanB.initial_front_congr
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_congr"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_congr"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_congr
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_congr"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_classical_front_unique"
#check @MethbokeAddon.WeakFouriermanB.initial_classical_front_unique
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_classical_front_unique"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_classical_front_unique"
#print axioms MethbokeAddon.WeakFouriermanB.initial_classical_front_unique
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_classical_front_unique"
