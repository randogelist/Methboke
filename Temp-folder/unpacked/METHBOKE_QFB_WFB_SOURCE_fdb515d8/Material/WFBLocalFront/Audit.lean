import WFBLocalFront.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology

-- Independently stated principal signature; no extra premise may be inferred.
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure),
    LocalPhysicalNSEFront ν T a u p →
    FourierBudgetFinite (fun t => datumFourierCoeff (u t)) T →
    MemLp (fun t => criticalSpatialNorm 6 (u t)) 4
      (volume.restrict (Ioo (0 : ℝ) T)) :=
  @local_front_fourier_budget_to_serrin

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.localFrontSpacetime_isOpen"
#check @MethbokeAddon.WeakFouriermanB.localFrontSpacetime_isOpen
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.localFrontSpacetime_isOpen"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.localFrontSpacetime_isOpen"
#print axioms MethbokeAddon.WeakFouriermanB.localFrontSpacetime_isOpen
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.localFrontSpacetime_isOpen"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_spatial_slice_contDiff"
#check @MethbokeAddon.WeakFouriermanB.local_spatial_slice_contDiff
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_spatial_slice_contDiff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_spatial_slice_contDiff"
#print axioms MethbokeAddon.WeakFouriermanB.local_spatial_slice_contDiff
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_spatial_slice_contDiff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_eq_joint"
#check @MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_eq_joint
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_eq_joint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_eq_joint"
#print axioms MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_eq_joint
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_eq_joint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_continuousOn"
#check @MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_continuousOn
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_continuousOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_continuousOn"
#print axioms MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_continuousOn
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_continuousOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_spatialNorm_aestronglyMeasurable"
#check @MethbokeAddon.WeakFouriermanB.local_spatialNorm_aestronglyMeasurable
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_spatialNorm_aestronglyMeasurable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_spatialNorm_aestronglyMeasurable"
#print axioms MethbokeAddon.WeakFouriermanB.local_spatialNorm_aestronglyMeasurable
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_spatialNorm_aestronglyMeasurable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_spatialNorm_six_aestronglyMeasurable"
#check @MethbokeAddon.WeakFouriermanB.local_spatialNorm_six_aestronglyMeasurable
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_spatialNorm_six_aestronglyMeasurable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_spatialNorm_six_aestronglyMeasurable"
#print axioms MethbokeAddon.WeakFouriermanB.local_spatialNorm_six_aestronglyMeasurable
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_spatialNorm_six_aestronglyMeasurable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_physicalEnergy_aestronglyMeasurable"
#check @MethbokeAddon.WeakFouriermanB.local_physicalEnergy_aestronglyMeasurable
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_physicalEnergy_aestronglyMeasurable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_physicalEnergy_aestronglyMeasurable"
#print axioms MethbokeAddon.WeakFouriermanB.local_physicalEnergy_aestronglyMeasurable
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_physicalEnergy_aestronglyMeasurable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physicalDissipation_eq_sum_coordinateEnergy"
#check @MethbokeAddon.WeakFouriermanB.physicalDissipation_eq_sum_coordinateEnergy
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physicalDissipation_eq_sum_coordinateEnergy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physicalDissipation_eq_sum_coordinateEnergy"
#print axioms MethbokeAddon.WeakFouriermanB.physicalDissipation_eq_sum_coordinateEnergy
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physicalDissipation_eq_sum_coordinateEnergy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_physicalDissipation_aestronglyMeasurable"
#check @MethbokeAddon.WeakFouriermanB.local_physicalDissipation_aestronglyMeasurable
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_physicalDissipation_aestronglyMeasurable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_physicalDissipation_aestronglyMeasurable"
#print axioms MethbokeAddon.WeakFouriermanB.local_physicalDissipation_aestronglyMeasurable
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_physicalDissipation_aestronglyMeasurable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_hasDerivAt_real_cube_integral"
#check @MethbokeAddon.WeakFouriermanB.local_hasDerivAt_real_cube_integral
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_hasDerivAt_real_cube_integral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_hasDerivAt_real_cube_integral"
#print axioms MethbokeAddon.WeakFouriermanB.local_hasDerivAt_real_cube_integral
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_hasDerivAt_real_cube_integral"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_real_cube_integral_continuousOn_Icc"
#check @MethbokeAddon.WeakFouriermanB.local_real_cube_integral_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_real_cube_integral_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_real_cube_integral_continuousOn_Icc"
#print axioms MethbokeAddon.WeakFouriermanB.local_real_cube_integral_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_real_cube_integral_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_timeDerivative_eq_joint"
#check @MethbokeAddon.WeakFouriermanB.local_timeDerivative_eq_joint
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_timeDerivative_eq_joint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_timeDerivative_eq_joint"
#print axioms MethbokeAddon.WeakFouriermanB.local_timeDerivative_eq_joint
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_timeDerivative_eq_joint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_time_hasDerivAt"
#check @MethbokeAddon.WeakFouriermanB.local_time_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_time_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_time_hasDerivAt"
#print axioms MethbokeAddon.WeakFouriermanB.local_time_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_time_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_timeDerivative_continuousOn"
#check @MethbokeAddon.WeakFouriermanB.local_timeDerivative_continuousOn
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_timeDerivative_continuousOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_timeDerivative_continuousOn"
#print axioms MethbokeAddon.WeakFouriermanB.local_timeDerivative_continuousOn
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_timeDerivative_continuousOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_physicalEnergy_hasDerivAt"
#check @MethbokeAddon.WeakFouriermanB.local_physicalEnergy_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_physicalEnergy_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_physicalEnergy_hasDerivAt"
#print axioms MethbokeAddon.WeakFouriermanB.local_physicalEnergy_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_physicalEnergy_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_smooth_energy_pairing"
#check @MethbokeAddon.WeakFouriermanB.local_smooth_energy_pairing
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_smooth_energy_pairing"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_smooth_energy_pairing"
#print axioms MethbokeAddon.WeakFouriermanB.local_smooth_energy_pairing
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_smooth_energy_pairing"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_nse_energy_hasDeriv"
#check @MethbokeAddon.WeakFouriermanB.local_nse_energy_hasDeriv
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_nse_energy_hasDeriv"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_nse_energy_hasDeriv"
#print axioms MethbokeAddon.WeakFouriermanB.local_nse_energy_hasDeriv
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_nse_energy_hasDeriv"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_nse_energy_identity"
#check @MethbokeAddon.WeakFouriermanB.local_nse_energy_identity
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_nse_energy_identity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_nse_energy_identity"
#print axioms MethbokeAddon.WeakFouriermanB.local_nse_energy_identity
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_nse_energy_identity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_nse_energy_le_earlier"
#check @MethbokeAddon.WeakFouriermanB.local_nse_energy_le_earlier
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_nse_energy_le_earlier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_nse_energy_le_earlier"
#print axioms MethbokeAddon.WeakFouriermanB.local_nse_energy_le_earlier
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_nse_energy_le_earlier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_nse_energy_le_initial_trace"
#check @MethbokeAddon.WeakFouriermanB.local_nse_energy_le_initial_trace
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_nse_energy_le_initial_trace"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_nse_energy_le_initial_trace"
#print axioms MethbokeAddon.WeakFouriermanB.local_nse_energy_le_initial_trace
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_nse_energy_le_initial_trace"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physicalEnergy_eq_L2Representative_norm_sq"
#check @MethbokeAddon.WeakFouriermanB.physicalEnergy_eq_L2Representative_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physicalEnergy_eq_L2Representative_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physicalEnergy_eq_L2Representative_norm_sq"
#print axioms MethbokeAddon.WeakFouriermanB.physicalEnergy_eq_L2Representative_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physicalEnergy_eq_L2Representative_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.L2Representative_tendsto_of_strong_trace"
#check @MethbokeAddon.WeakFouriermanB.L2Representative_tendsto_of_strong_trace
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.L2Representative_tendsto_of_strong_trace"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.L2Representative_tendsto_of_strong_trace"
#print axioms MethbokeAddon.WeakFouriermanB.L2Representative_tendsto_of_strong_trace
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.L2Representative_tendsto_of_strong_trace"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physical_energy_tendsto_of_L2_trace"
#check @MethbokeAddon.WeakFouriermanB.physical_energy_tendsto_of_L2_trace
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physical_energy_tendsto_of_L2_trace"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physical_energy_tendsto_of_L2_trace"
#print axioms MethbokeAddon.WeakFouriermanB.physical_energy_tendsto_of_L2_trace
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physical_energy_tendsto_of_L2_trace"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_physical_energy_trace_of_strong_L2_trace"
#check @MethbokeAddon.WeakFouriermanB.local_physical_energy_trace_of_strong_L2_trace
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_physical_energy_trace_of_strong_L2_trace"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_physical_energy_trace_of_strong_L2_trace"
#print axioms MethbokeAddon.WeakFouriermanB.local_physical_energy_trace_of_strong_L2_trace
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_physical_energy_trace_of_strong_L2_trace"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_smooth_slices"
#check @MethbokeAddon.WeakFouriermanB.local_front_smooth_slices
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_front_smooth_slices"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_smooth_slices"
#print axioms MethbokeAddon.WeakFouriermanB.local_front_smooth_slices
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_front_smooth_slices"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_pressure_slice_smooth"
#check @MethbokeAddon.WeakFouriermanB.local_front_pressure_slice_smooth
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_front_pressure_slice_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_pressure_slice_smooth"
#print axioms MethbokeAddon.WeakFouriermanB.local_front_pressure_slice_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_front_pressure_slice_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_initial_energy_trace"
#check @MethbokeAddon.WeakFouriermanB.local_front_initial_energy_trace
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_front_initial_energy_trace"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_initial_energy_trace"
#print axioms MethbokeAddon.WeakFouriermanB.local_front_initial_energy_trace
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_front_initial_energy_trace"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_energy_bound"
#check @MethbokeAddon.WeakFouriermanB.local_front_energy_bound
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_front_energy_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_energy_bound"
#print axioms MethbokeAddon.WeakFouriermanB.local_front_energy_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_front_energy_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_fourier_budget_to_serrin"
#check @MethbokeAddon.WeakFouriermanB.local_front_fourier_budget_to_serrin
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_front_fourier_budget_to_serrin"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_fourier_budget_to_serrin"
#print axioms MethbokeAddon.WeakFouriermanB.local_front_fourier_budget_to_serrin
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_front_fourier_budget_to_serrin"

