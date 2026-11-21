import R0AnalyticCapAdmission.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology Interval

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.initial_front_subset_analytic_cap
example : ∀ (ε T : ℝ) (hε : 0 < ε),
    initialFrontSpacetime T ⊆ analyticCapSpacetime ε T :=
  @MethbokeAddon.WeakFouriermanB.initial_front_subset_analytic_cap

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.analytic_forward_cap_to_initial_classical
example : ∀ (ν ε T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hε : 0 < ε) (H : AnalyticForwardNSECap ν ε T a u p),
    InitialClassicalFront ν T a u p :=
  @MethbokeAddon.WeakFouriermanB.analytic_forward_cap_to_initial_classical

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission
example : ∀ (ν ε T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hε : 0 < ε)
    (hcap : cutoff (criticalL2Representative a) ν < T)
    (H : AnalyticForwardNSECap ν ε T a u p),
    ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      ∀ r ∈ Ico (0 : ℝ) T, U r = u r ∧ P r = p r :=
  @MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission_physical_cutoff
example : ∀ (ν ε T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hε : 0 < ε)
    (hcap : (physicalEnergy a) ^ 2 / (8 * Real.pi ^ 2 * ν ^ 5) < T)
    (H : AnalyticForwardNSECap ν ε T a u p),
    ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      ∀ r ∈ Ico (0 : ℝ) T, U r = u r ∧ P r = p r :=
  @MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission_physical_cutoff

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_subset_analytic_cap"
#check @MethbokeAddon.WeakFouriermanB.initial_front_subset_analytic_cap
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_subset_analytic_cap"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_subset_analytic_cap"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_subset_analytic_cap
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_subset_analytic_cap"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_forward_cap_to_initial_classical"
#check @MethbokeAddon.WeakFouriermanB.analytic_forward_cap_to_initial_classical
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.analytic_forward_cap_to_initial_classical"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_forward_cap_to_initial_classical"
#print axioms MethbokeAddon.WeakFouriermanB.analytic_forward_cap_to_initial_classical
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.analytic_forward_cap_to_initial_classical"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission"
#check @MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission"
#print axioms MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission_physical_cutoff"
#check @MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission_physical_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission_physical_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission_physical_cutoff"
#print axioms MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission_physical_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.analytic_forward_cap_admission_physical_cutoff"

