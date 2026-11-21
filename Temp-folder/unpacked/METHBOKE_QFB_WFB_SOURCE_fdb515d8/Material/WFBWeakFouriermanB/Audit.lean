import WFBWeakFouriermanB.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory SingularClosure QuasiFeffermanB
open scoped ENNReal
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.smooth_datum_maximal_classical_front_exists
example : ∀ (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a),
    ∃ Tmax : ℝ≥0∞, ∃ (u : Velocity) (p : Pressure),
      MaximalClassicalFront ν a u p Tmax :=
  @MethbokeAddon.WeakFouriermanB.smooth_datum_maximal_classical_front_exists

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.Weak_Fourierman_B
example : ∀ (ν : ℝ) (hν : 0 < ν) (a : Field) (_ha : SmoothSigmaZero a)
    (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (H : MaximalClassicalFront ν a u p Tmax)
    (hbudget : FourierBudgetFinite (fun t => datumFourierCoeff (u t))
      (min Tmax (ENNReal.ofReal (cutoff (criticalL2Representative a) ν))).toReal),
    Tmax = ⊤ ∧ ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < Tmax → U t = u t ∧ P t = p t :=
  @MethbokeAddon.WeakFouriermanB.Weak_Fourierman_B

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_maximal_classical_front_exists"
#check @MethbokeAddon.WeakFouriermanB.smooth_datum_maximal_classical_front_exists
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.smooth_datum_maximal_classical_front_exists"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_maximal_classical_front_exists"
#print axioms MethbokeAddon.WeakFouriermanB.smooth_datum_maximal_classical_front_exists
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.smooth_datum_maximal_classical_front_exists"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.Weak_Fourierman_B"
#check @MethbokeAddon.WeakFouriermanB.Weak_Fourierman_B
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.Weak_Fourierman_B"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.Weak_Fourierman_B"
#print axioms MethbokeAddon.WeakFouriermanB.Weak_Fourierman_B
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.Weak_Fourierman_B"
