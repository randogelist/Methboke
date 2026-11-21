import WFBHomogeneousBudget.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology

-- Independently stated principal signature; no extra premise may be inferred.
example : ∀ (u : Velocity) (T : ℝ),
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T) →
    (∀ t ∈ Ioo (0 : ℝ) T, SpatialPeriodic (u t)) →
    (∀ t ∈ Ioo (0 : ℝ) T, MeanZero (u t)) →
    FourierBudgetFinite (fun t => datumFourierCoeff (u t)) T →
    MemLp (fun t => criticalSpatialNorm 6 (u t)) 4
      (volume.restrict (Ioo (0 : ℝ) T)) :=
  @local_homogeneous_fourier_budget_to_serrin

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.meanZero_datumFourierCoeff_meanZero"
#check @MethbokeAddon.WeakFouriermanB.meanZero_datumFourierCoeff_meanZero
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.meanZero_datumFourierCoeff_meanZero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.meanZero_datumFourierCoeff_meanZero"
#print axioms MethbokeAddon.WeakFouriermanB.meanZero_datumFourierCoeff_meanZero
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.meanZero_datumFourierCoeff_meanZero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_periodic_meanZero_energy_le_dissipation"
#check @MethbokeAddon.WeakFouriermanB.smooth_periodic_meanZero_energy_le_dissipation
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.smooth_periodic_meanZero_energy_le_dissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_periodic_meanZero_energy_le_dissipation"
#print axioms MethbokeAddon.WeakFouriermanB.smooth_periodic_meanZero_energy_le_dissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.smooth_periodic_meanZero_energy_le_dissipation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.SMOOTH_MEAN_ZERO_HOMOGENEOUS_L6_FOURTH"
#check @MethbokeAddon.WeakFouriermanB.SMOOTH_MEAN_ZERO_HOMOGENEOUS_L6_FOURTH
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.SMOOTH_MEAN_ZERO_HOMOGENEOUS_L6_FOURTH"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.SMOOTH_MEAN_ZERO_HOMOGENEOUS_L6_FOURTH"
#print axioms MethbokeAddon.WeakFouriermanB.SMOOTH_MEAN_ZERO_HOMOGENEOUS_L6_FOURTH
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.SMOOTH_MEAN_ZERO_HOMOGENEOUS_L6_FOURTH"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_pos"
#check @MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_pos
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_pos"
#print axioms MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_bound"
#check @MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_bound
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_bound"
#print axioms MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.homogeneous_l6_fourth_integrable_of_dissipation_square"
#check @MethbokeAddon.WeakFouriermanB.homogeneous_l6_fourth_integrable_of_dissipation_square
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.homogeneous_l6_fourth_integrable_of_dissipation_square"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.homogeneous_l6_fourth_integrable_of_dissipation_square"
#print axioms MethbokeAddon.WeakFouriermanB.homogeneous_l6_fourth_integrable_of_dissipation_square
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.homogeneous_l6_fourth_integrable_of_dissipation_square"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.homogeneous_serrin_of_dissipation_square"
#check @MethbokeAddon.WeakFouriermanB.homogeneous_serrin_of_dissipation_square
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.homogeneous_serrin_of_dissipation_square"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.homogeneous_serrin_of_dissipation_square"
#print axioms MethbokeAddon.WeakFouriermanB.homogeneous_serrin_of_dissipation_square
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.homogeneous_serrin_of_dissipation_square"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.homogeneous_dissipation_square_integrable_of_fourier_budget"
#check @MethbokeAddon.WeakFouriermanB.homogeneous_dissipation_square_integrable_of_fourier_budget
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.homogeneous_dissipation_square_integrable_of_fourier_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.homogeneous_dissipation_square_integrable_of_fourier_budget"
#print axioms MethbokeAddon.WeakFouriermanB.homogeneous_dissipation_square_integrable_of_fourier_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.homogeneous_dissipation_square_integrable_of_fourier_budget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.homogeneous_physical_fourier_budget_to_serrin"
#check @MethbokeAddon.WeakFouriermanB.homogeneous_physical_fourier_budget_to_serrin
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.homogeneous_physical_fourier_budget_to_serrin"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.homogeneous_physical_fourier_budget_to_serrin"
#print axioms MethbokeAddon.WeakFouriermanB.homogeneous_physical_fourier_budget_to_serrin
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.homogeneous_physical_fourier_budget_to_serrin"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_homogeneous_fourier_budget_to_serrin"
#check @MethbokeAddon.WeakFouriermanB.local_homogeneous_fourier_budget_to_serrin
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_homogeneous_fourier_budget_to_serrin"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_homogeneous_fourier_budget_to_serrin"
#print axioms MethbokeAddon.WeakFouriermanB.local_homogeneous_fourier_budget_to_serrin
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_homogeneous_fourier_budget_to_serrin"

