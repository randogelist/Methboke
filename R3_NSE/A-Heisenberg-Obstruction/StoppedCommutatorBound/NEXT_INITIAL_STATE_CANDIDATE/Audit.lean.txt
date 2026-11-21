import R3EhrenfestInitialState.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace R3EhrenfestInitialState.ExpectedTypes

open MethbokeAddon.R3Ehrenfest
open MethbokeAddon.R3Ehrenfest.InitialState
open MethbokeAddon.R3Ehrenfest.Carrier
open MethbokeAddon.R3Ehrenfest.Bandlimited
open MethbokeAddon.QuasiFeffermanA

example (n : ℕ) (a : SmoothDatum) : BandlimitedSolenoidal n :=
  smoothDatumInitialState n a

example (n : ℕ) (a : SmoothDatum) :
    ((smoothDatumInitialState n a : BandlimitedSolenoidal n) : SpatialL2) =
      MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff n
        (a.value.toLp 2 volume) :=
  smoothDatumInitialState_coe n a

example (n : ℕ) (a : SmoothDatum) :
    MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff n
        (smoothDatumInitialState n a : SpatialL2) =
      (smoothDatumInitialState n a : SpatialL2) :=
  smoothDatumInitialState_cutoff_fixed n a

example (n : ℕ) (a : SmoothDatum) :
    realLeray (smoothDatumInitialState n a : SpatialL2) =
      (smoothDatumInitialState n a : SpatialL2) :=
  smoothDatumInitialState_leray_fixed n a

example (n : ℕ) (a : SmoothDatum) :
    Solenoidal (smoothDatumInitialState n a : SpatialL2) :=
  smoothDatumInitialState_solenoidal n a

example (n : ℕ) (a : SmoothDatum) :
    ‖smoothDatumInitialState n a‖ ≤ ‖a.value.toLp 2 volume‖ :=
  norm_smoothDatumInitialState_le n a

example (n : ℕ) (a : SmoothDatum) : PhysicalH2 :=
  smoothDatumInitialH2 n a

example (n : ℕ) (a : SmoothDatum) :
    physicalH2Velocity (smoothDatumInitialH2 n a) =
      MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff n
        (a.value.toLp 2 volume) :=
  smoothDatumInitialH2_velocity n a

example (n : ℕ) (a : SmoothDatum) (j : Fin 3) :
    physicalH2Gradient j (smoothDatumInitialH2 n a) =
      cutoffDerivative n j (a.value.toLp 2 volume) :=
  smoothDatumInitialH2_gradient n a j

example (n : ℕ) (a : SmoothDatum) (j k : Fin 3) :
    physicalH2Hessian j k (smoothDatumInitialH2 n a) =
      cutoffDerivative n k (cutoffDerivative n j (a.value.toLp 2 volume)) :=
  smoothDatumInitialH2_hessian n a j k

example (n : ℕ) (a : SmoothDatum) :
    physicalH2Velocity (smoothDatumInitialH2 n a) =
      (smoothDatumInitialState n a : SpatialL2) :=
  smoothDatumInitialH2_velocity_eq_state n a

example (n : ℕ) (a : SmoothDatum) :
    ‖smoothDatumInitialH2 n a‖ ≤
      sharpCutoffH2Bound n * ‖a.value.toLp 2 volume‖ :=
  norm_smoothDatumInitialH2_le n a

example (n : ℕ) (a : SmoothDatum) : PhysicalH2Sigma :=
  smoothDatumInitialH2Sigma n a

example (n : ℕ) (a : SmoothDatum) :
    physicalH2SigmaToH2LI (smoothDatumInitialH2Sigma n a) =
      smoothDatumInitialH2 n a :=
  smoothDatumInitialH2Sigma_toH2 n a

example (n : ℕ) (a : SmoothDatum) :
    physicalH2Velocity
        (physicalH2SigmaToH2LI (smoothDatumInitialH2Sigma n a)) =
      (smoothDatumInitialState n a : SpatialL2) :=
  smoothDatumInitialH2Sigma_velocity n a

example (n : ℕ) (a : SmoothDatum) :
    bandlimitedProject n (smoothDatumInitialState n a : SpatialL2) =
      smoothDatumInitialState n a :=
  smoothDatumInitialState_projected n a

end R3EhrenfestInitialState.ExpectedTypes

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState"
#check @MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_coe"
#check @MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_coe
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_coe"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_coe"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_coe
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_coe"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_cutoff_fixed"
#check @MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_cutoff_fixed
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_cutoff_fixed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_cutoff_fixed"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_cutoff_fixed
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_cutoff_fixed"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_leray_fixed"
#check @MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_leray_fixed
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_leray_fixed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_leray_fixed"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_leray_fixed
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_leray_fixed"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_solenoidal"
#check @MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_solenoidal"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.norm_smoothDatumInitialState_le"
#check @MethbokeAddon.R3Ehrenfest.InitialState.norm_smoothDatumInitialState_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.norm_smoothDatumInitialState_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.norm_smoothDatumInitialState_le"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.norm_smoothDatumInitialState_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.norm_smoothDatumInitialState_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2"
#check @MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_velocity"
#check @MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_velocity
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_velocity"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_gradient"
#check @MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_gradient
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_gradient"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_hessian"
#check @MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_hessian
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_hessian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_hessian"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_hessian
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_hessian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_velocity_eq_state"
#check @MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_velocity_eq_state
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_velocity_eq_state"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_velocity_eq_state"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_velocity_eq_state
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2_velocity_eq_state"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.norm_smoothDatumInitialH2_le"
#check @MethbokeAddon.R3Ehrenfest.InitialState.norm_smoothDatumInitialH2_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.norm_smoothDatumInitialH2_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.norm_smoothDatumInitialH2_le"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.norm_smoothDatumInitialH2_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.norm_smoothDatumInitialH2_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma"
#check @MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma_toH2"
#check @MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma_toH2
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma_toH2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma_toH2"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma_toH2
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma_toH2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma_velocity"
#check @MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma_velocity
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma_velocity"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialH2Sigma_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_projected"
#check @MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_projected
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_projected"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_projected"
#print axioms MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_projected
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.InitialState.smoothDatumInitialState_projected"
