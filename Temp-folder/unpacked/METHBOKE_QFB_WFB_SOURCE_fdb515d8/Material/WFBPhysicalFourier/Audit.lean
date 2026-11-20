import WFBPhysicalFourier.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology

-- Independently stated principal signature; no extra premise may be inferred.
example : ∀ (v : Field), SmoothSigmaZero v →
    physicalDissipation v =
      (4 * Real.pi ^ 2) * FourierEnstrophy (datumFourierCoeff v) :=
  @smoothSigmaZero_dissipation_eq_fourierEnstrophy

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_nonneg"
#check @MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_nonneg"
#print axioms MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_zero_frequency"
#check @MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_zero_frequency
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_zero_frequency"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_zero_frequency"
#print axioms MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_zero_frequency
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_zero_frequency"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.fourierEnstrophy_nonneg"
#check @MethbokeAddon.WeakFouriermanB.fourierEnstrophy_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.fourierEnstrophy_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.fourierEnstrophy_nonneg"
#print axioms MethbokeAddon.WeakFouriermanB.fourierEnstrophy_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.fourierEnstrophy_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.fourierEnstrophy_summable"
#check @MethbokeAddon.WeakFouriermanB.fourierEnstrophy_summable
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.fourierEnstrophy_summable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.fourierEnstrophy_summable"
#print axioms MethbokeAddon.WeakFouriermanB.fourierEnstrophy_summable
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.fourierEnstrophy_summable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.ofReal_fourierEnstrophy_eq_extended"
#check @MethbokeAddon.WeakFouriermanB.ofReal_fourierEnstrophy_eq_extended
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.ofReal_fourierEnstrophy_eq_extended"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.ofReal_fourierEnstrophy_eq_extended"
#print axioms MethbokeAddon.WeakFouriermanB.ofReal_fourierEnstrophy_eq_extended
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.ofReal_fourierEnstrophy_eq_extended"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.extendedFourierEnstrophy_ne_top"
#check @MethbokeAddon.WeakFouriermanB.extendedFourierEnstrophy_ne_top
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.extendedFourierEnstrophy_ne_top"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.extendedFourierEnstrophy_ne_top"
#print axioms MethbokeAddon.WeakFouriermanB.extendedFourierEnstrophy_ne_top
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.extendedFourierEnstrophy_ne_top"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.fourierEnstrophy_eq_modes_components"
#check @MethbokeAddon.WeakFouriermanB.fourierEnstrophy_eq_modes_components
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.fourierEnstrophy_eq_modes_components"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.fourierEnstrophy_eq_modes_components"
#print axioms MethbokeAddon.WeakFouriermanB.fourierEnstrophy_eq_modes_components
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.fourierEnstrophy_eq_modes_components"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.criticalH1_norm_sq_eq_fourierEnstrophy"
#check @MethbokeAddon.WeakFouriermanB.criticalH1_norm_sq_eq_fourierEnstrophy
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.criticalH1_norm_sq_eq_fourierEnstrophy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.criticalH1_norm_sq_eq_fourierEnstrophy"
#print axioms MethbokeAddon.WeakFouriermanB.criticalH1_norm_sq_eq_fourierEnstrophy
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.criticalH1_norm_sq_eq_fourierEnstrophy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.smoothSynthesis_dissipation_eq_fourierEnstrophy"
#check @MethbokeAddon.WeakFouriermanB.smoothSynthesis_dissipation_eq_fourierEnstrophy
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.smoothSynthesis_dissipation_eq_fourierEnstrophy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.smoothSynthesis_dissipation_eq_fourierEnstrophy"
#print axioms MethbokeAddon.WeakFouriermanB.smoothSynthesis_dissipation_eq_fourierEnstrophy
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.smoothSynthesis_dissipation_eq_fourierEnstrophy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physicalH1_of_smooth_periodic"
#check @MethbokeAddon.WeakFouriermanB.physicalH1_of_smooth_periodic
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physicalH1_of_smooth_periodic"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physicalH1_of_smooth_periodic"
#print axioms MethbokeAddon.WeakFouriermanB.physicalH1_of_smooth_periodic
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physicalH1_of_smooth_periodic"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.smoothFourierSynthesis_datum_eq"
#check @MethbokeAddon.WeakFouriermanB.smoothFourierSynthesis_datum_eq
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.smoothFourierSynthesis_datum_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.smoothFourierSynthesis_datum_eq"
#print axioms MethbokeAddon.WeakFouriermanB.smoothFourierSynthesis_datum_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.smoothFourierSynthesis_datum_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.smoothSigmaZero_fourierEnstrophy_summable"
#check @MethbokeAddon.WeakFouriermanB.smoothSigmaZero_fourierEnstrophy_summable
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.smoothSigmaZero_fourierEnstrophy_summable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.smoothSigmaZero_fourierEnstrophy_summable"
#print axioms MethbokeAddon.WeakFouriermanB.smoothSigmaZero_fourierEnstrophy_summable
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.smoothSigmaZero_fourierEnstrophy_summable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.smoothSigmaZero_dissipation_eq_fourierEnstrophy"
#check @MethbokeAddon.WeakFouriermanB.smoothSigmaZero_dissipation_eq_fourierEnstrophy
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.smoothSigmaZero_dissipation_eq_fourierEnstrophy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.smoothSigmaZero_dissipation_eq_fourierEnstrophy"
#print axioms MethbokeAddon.WeakFouriermanB.smoothSigmaZero_dissipation_eq_fourierEnstrophy
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.smoothSigmaZero_dissipation_eq_fourierEnstrophy"

