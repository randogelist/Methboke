import WFBWFBRootAssembly.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set SingularClosure QuasiFeffermanB
open scoped ENNReal
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.maximal_classical_front_global_of_strict_cutoff
example : ∀ (ν : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (H : MaximalClassicalFront ν a u p Tmax)
    (hcut : ENNReal.ofReal (cutoff (criticalL2Representative a) ν) < Tmax),
    Tmax = ⊤ ∧ ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < Tmax → U t = u t ∧ P t = p t :=
  @MethbokeAddon.WeakFouriermanB.maximal_classical_front_global_of_strict_cutoff

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_front_global_of_strict_cutoff"
#check @MethbokeAddon.WeakFouriermanB.maximal_classical_front_global_of_strict_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.maximal_classical_front_global_of_strict_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_front_global_of_strict_cutoff"
#print axioms MethbokeAddon.WeakFouriermanB.maximal_classical_front_global_of_strict_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.maximal_classical_front_global_of_strict_cutoff"
