import R0AnalyticTwoSidedCap.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology Interval

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.analytic_cap_time_differentiableAt
example : ∀ (ε T : ℝ) (u : Velocity)
    (hu : AnalyticOnNhd ℝ (fun z : ℝ × Vec => u z.1 z.2) (analyticCapSpacetime ε T))
    (t : ℝ) (ht : t ∈ Ioo (-ε) T) (x : Vec),
    DifferentiableAt ℝ (fun r : ℝ => u r x) t :=
  @MethbokeAddon.WeakFouriermanB.analytic_cap_time_differentiableAt

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.analytic_cap_forward_timeDerivative_eq_deriv
example : ∀ (ε T : ℝ) (u : Velocity)
    (hu : AnalyticOnNhd ℝ (fun z : ℝ × Vec => u z.1 z.2) (analyticCapSpacetime ε T))
    (t : ℝ) (ht : t ∈ Ioo (-ε) T) (ht0 : 0 ≤ t) (x : Vec),
    timeDerivative u t x = deriv (fun r : ℝ => u r x) t :=
  @MethbokeAddon.WeakFouriermanB.analytic_cap_forward_timeDerivative_eq_deriv

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_to_forward
example : ∀ (ν ε T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hε : 0 < ε) (H : AnalyticTwoSidedNSECap ν ε T a u p),
    AnalyticForwardNSECap ν ε T a u p :=
  @MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_to_forward

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission
example : ∀ (ν ε T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hε : 0 < ε)
    (hcap : cutoff (criticalL2Representative a) ν < T)
    (H : AnalyticTwoSidedNSECap ν ε T a u p),
    ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      ∀ r ∈ Ico (0 : ℝ) T, U r = u r ∧ P r = p r :=
  @MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission_physical_cutoff
example : ∀ (ν ε T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hε : 0 < ε)
    (hcap : (physicalEnergy a) ^ 2 / (8 * Real.pi ^ 2 * ν ^ 5) < T)
    (H : AnalyticTwoSidedNSECap ν ε T a u p),
    ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      ∀ r ∈ Ico (0 : ℝ) T, U r = u r ∧ P r = p r :=
  @MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission_physical_cutoff

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_cap_time_differentiableAt"
#check @MethbokeAddon.WeakFouriermanB.analytic_cap_time_differentiableAt
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.analytic_cap_time_differentiableAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_cap_time_differentiableAt"
#print axioms MethbokeAddon.WeakFouriermanB.analytic_cap_time_differentiableAt
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.analytic_cap_time_differentiableAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_cap_forward_timeDerivative_eq_deriv"
#check @MethbokeAddon.WeakFouriermanB.analytic_cap_forward_timeDerivative_eq_deriv
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.analytic_cap_forward_timeDerivative_eq_deriv"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_cap_forward_timeDerivative_eq_deriv"
#print axioms MethbokeAddon.WeakFouriermanB.analytic_cap_forward_timeDerivative_eq_deriv
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.analytic_cap_forward_timeDerivative_eq_deriv"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_to_forward"
#check @MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_to_forward
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_to_forward"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_to_forward"
#print axioms MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_to_forward
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_to_forward"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission"
#check @MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission"
#print axioms MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission_physical_cutoff"
#check @MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission_physical_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission_physical_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission_physical_cutoff"
#print axioms MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission_physical_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.analytic_two_sided_cap_admission_physical_cutoff"

