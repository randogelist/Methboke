import R0FiniteCapAdmission.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology Interval

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.finite_cap_classical_admission
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hcap : cutoff (criticalL2Representative a) ν < T)
    (H : InitialClassicalFront ν T a u p),
    ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      ∀ r ∈ Ico (0 : ℝ) T, U r = u r ∧ P r = p r :=
  @MethbokeAddon.WeakFouriermanB.finite_cap_classical_admission

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.finite_cap_classical_admission"
#check @MethbokeAddon.WeakFouriermanB.finite_cap_classical_admission
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.finite_cap_classical_admission"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.finite_cap_classical_admission"
#print axioms MethbokeAddon.WeakFouriermanB.finite_cap_classical_admission
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.finite_cap_classical_admission"

