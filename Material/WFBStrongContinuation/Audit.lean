import WFBStrongContinuation.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped ENNReal
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_eq_top_of_uniform_H1
example : ∀ (ν R : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (H : MaximalClassicalFront ν a u p Tmax)
    (hbound : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < Tmax →
      physicalH1Square (u t) ≤ R),
    Tmax = ⊤ :=
  @MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_eq_top_of_uniform_H1

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_eq_top_of_uniform_H1"
#check @MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_eq_top_of_uniform_H1
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_eq_top_of_uniform_H1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_eq_top_of_uniform_H1"
#print axioms MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_eq_top_of_uniform_H1
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.maximal_classical_lifetime_eq_top_of_uniform_H1"
