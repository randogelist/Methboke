import WFBLocalExistence.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped Interval
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_initial_classical_front_exists
example : ∀ (ν R : ℝ) (hν : 0 < ν) (hR : 0 ≤ R)
    (a : Field) (ha : SmoothSigmaZero a) (hinit : physicalDissipation a ≤ R),
    ∃ u : Velocity, ∃ p : Pressure,
      InitialClassicalFront ν (localGalerkinTime ν R) a u p :=
  @MethbokeAddon.WeakFouriermanB.local_initial_classical_front_exists

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.uniform_H1_local_initial_classical_front_exists
example : ∀ (ν R : ℝ) (hν : 0 < ν) (hR : 0 ≤ R),
    ∃ T : ℝ, 0 < T ∧ ∀ a : Field, SmoothSigmaZero a → physicalH1Square a ≤ R →
      ∃ u : Velocity, ∃ p : Pressure, InitialClassicalFront ν T a u p :=
  @MethbokeAddon.WeakFouriermanB.uniform_H1_local_initial_classical_front_exists

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_initial_classical_front_exists"
#check @MethbokeAddon.WeakFouriermanB.local_initial_classical_front_exists
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_initial_classical_front_exists"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_initial_classical_front_exists"
#print axioms MethbokeAddon.WeakFouriermanB.local_initial_classical_front_exists
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_initial_classical_front_exists"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.uniform_H1_local_initial_classical_front_exists"
#check @MethbokeAddon.WeakFouriermanB.uniform_H1_local_initial_classical_front_exists
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.uniform_H1_local_initial_classical_front_exists"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.uniform_H1_local_initial_classical_front_exists"
#print axioms MethbokeAddon.WeakFouriermanB.uniform_H1_local_initial_classical_front_exists
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.uniform_H1_local_initial_classical_front_exists"
