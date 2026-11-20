import WFBPhysicalEndpointContinuation.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped ENNReal
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_extends_of_dissipation_square
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hT : 0 < T) (H : InitialClassicalFront ν T a u p)
    (hD : Integrable (fun t => physicalDissipation (u t) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) T))),
    ∃ S : ℝ, T < S ∧ ∃ (U : Velocity) (P : Pressure),
      InitialClassicalFront ν S a U P ∧
        ∀ t ∈ Ico (0 : ℝ) T, U t = u t ∧ P t = p t :=
  @MethbokeAddon.WeakFouriermanB.initial_front_extends_of_dissipation_square

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.maximal_classical_front_no_finite_dissipation_square
example : ∀ (ν : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (H : MaximalClassicalFront ν a u p Tmax)
    (hfinite : Tmax ≠ ⊤)
    (hD : Integrable (fun t => physicalDissipation (u t) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) Tmax.toReal))),
    False :=
  @MethbokeAddon.WeakFouriermanB.maximal_classical_front_no_finite_dissipation_square

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_extends_of_dissipation_square"
#check @MethbokeAddon.WeakFouriermanB.initial_front_extends_of_dissipation_square
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_extends_of_dissipation_square"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_extends_of_dissipation_square"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_extends_of_dissipation_square
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_extends_of_dissipation_square"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_front_no_finite_dissipation_square"
#check @MethbokeAddon.WeakFouriermanB.maximal_classical_front_no_finite_dissipation_square
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.maximal_classical_front_no_finite_dissipation_square"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_front_no_finite_dissipation_square"
#print axioms MethbokeAddon.WeakFouriermanB.maximal_classical_front_no_finite_dissipation_square
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.maximal_classical_front_no_finite_dissipation_square"
