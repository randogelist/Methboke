import WFBFourierBudget.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology

-- Independently stated principal signature; no extra premise may be inferred.
example : ∀ (u : ℝ → Field) (T E0 : ℝ),
    (∀ t ∈ Ioo (0 : ℝ) T, SmoothSigmaZero (u t)) →
    AEStronglyMeasurable (fun t => criticalSpatialNorm 6 (u t))
      (volume.restrict (Ioo (0 : ℝ) T)) →
    AEStronglyMeasurable (fun t => physicalDissipation (u t))
      (volume.restrict (Ioo (0 : ℝ) T)) →
    AEStronglyMeasurable (fun t => physicalEnergy (u t))
      (volume.restrict (Ioo (0 : ℝ) T)) →
    (∀ t ∈ Ioo (0 : ℝ) T, physicalEnergy (u t) ≤ E0) →
    FourierBudgetFinite (fun t => datumFourierCoeff (u t)) T →
    MemLp (fun t => criticalSpatialNorm 6 (u t)) 4
      (volume.restrict (Ioo (0 : ℝ) T)) :=
  @physical_fourier_budget_to_serrin

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.dissipation_square_integrable_of_fourier_budget"
#check @MethbokeAddon.WeakFouriermanB.dissipation_square_integrable_of_fourier_budget
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.dissipation_square_integrable_of_fourier_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.dissipation_square_integrable_of_fourier_budget"
#print axioms MethbokeAddon.WeakFouriermanB.dissipation_square_integrable_of_fourier_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.dissipation_square_integrable_of_fourier_budget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_serrin_of_energy_and_dissipation"
#check @MethbokeAddon.WeakFouriermanB.local_serrin_of_energy_and_dissipation
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_serrin_of_energy_and_dissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_serrin_of_energy_and_dissipation"
#print axioms MethbokeAddon.WeakFouriermanB.local_serrin_of_energy_and_dissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_serrin_of_energy_and_dissipation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physical_energy_square_integrable_of_bound"
#check @MethbokeAddon.WeakFouriermanB.physical_energy_square_integrable_of_bound
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physical_energy_square_integrable_of_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physical_energy_square_integrable_of_bound"
#print axioms MethbokeAddon.WeakFouriermanB.physical_energy_square_integrable_of_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physical_energy_square_integrable_of_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_serrin_of_fourier_budget"
#check @MethbokeAddon.WeakFouriermanB.local_serrin_of_fourier_budget
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_serrin_of_fourier_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_serrin_of_fourier_budget"
#print axioms MethbokeAddon.WeakFouriermanB.local_serrin_of_fourier_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_serrin_of_fourier_budget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physical_fourier_budget_to_serrin"
#check @MethbokeAddon.WeakFouriermanB.physical_fourier_budget_to_serrin
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physical_fourier_budget_to_serrin"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physical_fourier_budget_to_serrin"
#print axioms MethbokeAddon.WeakFouriermanB.physical_fourier_budget_to_serrin
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physical_fourier_budget_to_serrin"

