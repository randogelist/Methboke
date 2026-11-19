import WFBMaximalClassicalFront.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set SingularClosure
open scoped ENNReal
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_front
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hT : 0 < T) (H : InitialClassicalFront ν T a u p),
    ∃ Tmax : ℝ≥0∞, ∃ (U : Velocity) (P : Pressure),
      MaximalClassicalFront ν a U P Tmax :=
  @MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_front

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_local_existence
example : ∀ (ν : ℝ) (hν : 0 < ν)
    (hLocal : ∀ b : Field, SmoothSigmaZero b →
      ∃ T : ℝ, 0 < T ∧ ∃ (v : Velocity) (q : Pressure),
        InitialClassicalFront ν T b v q)
    (a : Field) (ha : SmoothSigmaZero a),
    ∃ Tmax : ℝ≥0∞, ∃ (U : Velocity) (P : Pressure),
      MaximalClassicalFront ν a U P Tmax :=
  @MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_local_existence

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.maximal_classical_front_lifetime_unique
example : ∀ (ν : ℝ) (a : Field) (u v : Velocity) (p q : Pressure)
    (Tmax Smax : ℝ≥0∞)
    (H : MaximalClassicalFront ν a u p Tmax)
    (K : MaximalClassicalFront ν a v q Smax),
    Tmax = Smax :=
  @MethbokeAddon.WeakFouriermanB.maximal_classical_front_lifetime_unique

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.maximal_classical_front_unique
example : ∀ (ν : ℝ) (a : Field) (u v : Velocity) (p q : Pressure)
    (Tmax Smax : ℝ≥0∞)
    (H : MaximalClassicalFront ν a u p Tmax)
    (K : MaximalClassicalFront ν a v q Smax),
    Tmax = Smax ∧ ∀ r : ℝ, 0 ≤ r → ENNReal.ofReal r < Tmax →
      u r = v r ∧ p r = q r :=
  @MethbokeAddon.WeakFouriermanB.maximal_classical_front_unique

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_front"
#check @MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_front
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_front"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_front"
#print axioms MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_front
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_front"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_local_existence"
#check @MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_local_existence
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_local_existence"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_local_existence"
#print axioms MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_local_existence
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.maximal_classical_front_exists_of_local_existence"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_front_lifetime_unique"
#check @MethbokeAddon.WeakFouriermanB.maximal_classical_front_lifetime_unique
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.maximal_classical_front_lifetime_unique"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_front_lifetime_unique"
#print axioms MethbokeAddon.WeakFouriermanB.maximal_classical_front_lifetime_unique
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.maximal_classical_front_lifetime_unique"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_front_unique"
#check @MethbokeAddon.WeakFouriermanB.maximal_classical_front_unique
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.maximal_classical_front_unique"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_classical_front_unique"
#print axioms MethbokeAddon.WeakFouriermanB.maximal_classical_front_unique
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.maximal_classical_front_unique"
