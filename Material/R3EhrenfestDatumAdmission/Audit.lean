import R3EhrenfestDatumAdmission.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ContDiff LineDeriv

namespace R3EhrenfestDatumAdmission.ExpectedTypes

open MethbokeAddon.R3Ehrenfest
open MethbokeAddon.R3Ehrenfest.DatumAdmission
open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence

example (a : SmoothDatum) (x : Space) :
    (∑ j : Fin 3,
      (fderiv ℝ (a.value : Space → Space) x (coordinateVector j)) j) = 0 :=
  smoothDatum_divergence_sum a x

example (a : SmoothDatum) :
    spatialGradientTrace
      (fun j : Fin 3 => (∂_{coordinateVector j} a.value).toLp 2 volume) = 0 :=
  smoothDatum_spatialGradientTrace_eq_zero a

example (a : SmoothDatum) : Solenoidal (a.value.toLp 2 volume) :=
  smoothDatum_solenoidal a

example (a : SmoothDatum) : EnergyDatum := smoothDatumToEnergyDatum a
example (a : SmoothDatum) :
    (smoothDatumToEnergyDatum a).val = a.value.toLp 2 volume :=
  smoothDatumToEnergyDatum_val a

example (a : SmoothDatum) : PhysicalH1Sigma := smoothDatumToPhysicalH1Sigma a
example (a : SmoothDatum) :
    (smoothDatumToPhysicalH1Sigma a).val 0 = a.value.toLp 2 volume :=
  smoothDatumToPhysicalH1Sigma_velocity a

example (a : SmoothDatum) : PhysicalH2 := smoothDatumToPhysicalH2 a
example (a : SmoothDatum) :
    physicalH2Velocity (smoothDatumToPhysicalH2 a) = a.value.toLp 2 volume :=
  smoothDatumToPhysicalH2_velocity a
example (a : SmoothDatum) (j : Fin 3) :
    physicalH2Gradient j (smoothDatumToPhysicalH2 a) =
      (∂_{coordinateVector j} a.value).toLp 2 volume :=
  smoothDatumToPhysicalH2_gradient a j
example (a : SmoothDatum) (j k : Fin 3) :
    physicalH2Hessian j k (smoothDatumToPhysicalH2 a) =
      (∂_{coordinateVector k} (∂_{coordinateVector j} a.value)).toLp 2 volume :=
  smoothDatumToPhysicalH2_hessian a j k

example (a : SmoothDatum) : PhysicalH2Sigma := smoothDatumToPhysicalH2Sigma a
example (a : SmoothDatum) :
    physicalH2SigmaToH2LI (smoothDatumToPhysicalH2Sigma a) =
      smoothDatumToPhysicalH2 a :=
  smoothDatumToPhysicalH2Sigma_toH2 a
example (a : SmoothDatum) :
    physicalH2Velocity
        (physicalH2SigmaToH2LI (smoothDatumToPhysicalH2Sigma a)) =
      a.value.toLp 2 volume :=
  smoothDatumToPhysicalH2Sigma_velocity a
example (a : SmoothDatum) :
    Solenoidal
      (physicalH2Velocity
        (physicalH2SigmaToH2LI (smoothDatumToPhysicalH2Sigma a))) :=
  smoothDatumToPhysicalH2Sigma_solenoidal a

end R3EhrenfestDatumAdmission.ExpectedTypes

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_divergence_sum"
#check @MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_divergence_sum
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_divergence_sum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_divergence_sum"
#print axioms MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_divergence_sum
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_divergence_sum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_spatialGradientTrace_eq_zero"
#check @MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_spatialGradientTrace_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_spatialGradientTrace_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_spatialGradientTrace_eq_zero"
#print axioms MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_spatialGradientTrace_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_spatialGradientTrace_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_solenoidal"
#check @MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_solenoidal"
#print axioms MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatum_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToEnergyDatum"
#check @MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToEnergyDatum
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToEnergyDatum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToEnergyDatum"
#print axioms MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToEnergyDatum
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToEnergyDatum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToEnergyDatum_val"
#check @MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToEnergyDatum_val
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToEnergyDatum_val"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToEnergyDatum_val"
#print axioms MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToEnergyDatum_val
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToEnergyDatum_val"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH1Sigma"
#check @MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH1Sigma
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH1Sigma"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH1Sigma"
#print axioms MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH1Sigma
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH1Sigma"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH1Sigma_velocity"
#check @MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH1Sigma_velocity
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH1Sigma_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH1Sigma_velocity"
#print axioms MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH1Sigma_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH1Sigma_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2"
#check @MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2"
#print axioms MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_velocity"
#check @MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_velocity
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_velocity"
#print axioms MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_gradient"
#check @MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_gradient
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_gradient"
#print axioms MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_hessian"
#check @MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_hessian
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_hessian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_hessian"
#print axioms MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_hessian
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2_hessian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma"
#check @MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma"
#print axioms MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_toH2"
#check @MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_toH2
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_toH2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_toH2"
#print axioms MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_toH2
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_toH2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_velocity"
#check @MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_velocity
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_velocity"
#print axioms MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_solenoidal"
#check @MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_solenoidal"
#print axioms MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DatumAdmission.smoothDatumToPhysicalH2Sigma_solenoidal"
