import EhrenfestObstructionRoot.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-! Independent exact consumer types; external evidence pending. -/


section Consumer1
open Set Filter SingularClosure
open MethbokeAddon.WeakFouriermanB
open MethbokeAddon.EhrenfestObstruction

example : ∀ (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar gamma : ℝ) (R : ℕ → ℝ),
    StoppedForDatum ν hν a eStar gamma R →
    ∀ (S : ℝ) (u : Velocity) (p : Pressure),
      InitialClassicalFront ν S a.val u p → 1 / gamma < S → False :=
  @stopped_forbids_initial_front

example : ∀ (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar gamma : ℝ) (R : ℕ → ℝ),
    StoppedForDatum ν hν a eStar gamma R →
    ∀ (u : Velocity) (p : Pressure), GlobalSmoothNSE ν a.val u p → False :=
  @stopped_forbids_global_smooth

example : ∀ (ν : ℝ), 0 < ν → StoppedCommutatorBound ν → Not (NSE_B ν) :=
  @EHRENFEST_OBSTRUCTION_DYNAMICAL

example : ∀ (ν : ℝ), 0 < ν → StoppedCommutatorBound ν → Not (NSE_B ν) :=
  @EHRENFEST_OBSTRUCTION
end Consumer1


#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_forbids_initial_front"
#check @MethbokeAddon.EhrenfestObstruction.stopped_forbids_initial_front
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.stopped_forbids_initial_front"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_forbids_initial_front"
#print axioms MethbokeAddon.EhrenfestObstruction.stopped_forbids_initial_front
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.stopped_forbids_initial_front"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_forbids_global_smooth"
#check @MethbokeAddon.EhrenfestObstruction.stopped_forbids_global_smooth
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.stopped_forbids_global_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_forbids_global_smooth"
#print axioms MethbokeAddon.EhrenfestObstruction.stopped_forbids_global_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.stopped_forbids_global_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.EHRENFEST_OBSTRUCTION_DYNAMICAL"
#check @MethbokeAddon.EhrenfestObstruction.EHRENFEST_OBSTRUCTION_DYNAMICAL
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.EHRENFEST_OBSTRUCTION_DYNAMICAL"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.EHRENFEST_OBSTRUCTION_DYNAMICAL"
#print axioms MethbokeAddon.EhrenfestObstruction.EHRENFEST_OBSTRUCTION_DYNAMICAL
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.EHRENFEST_OBSTRUCTION_DYNAMICAL"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.EHRENFEST_OBSTRUCTION"
#check @MethbokeAddon.EhrenfestObstruction.EHRENFEST_OBSTRUCTION
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.EHRENFEST_OBSTRUCTION"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.EHRENFEST_OBSTRUCTION"
#print axioms MethbokeAddon.EhrenfestObstruction.EHRENFEST_OBSTRUCTION
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.EHRENFEST_OBSTRUCTION"
