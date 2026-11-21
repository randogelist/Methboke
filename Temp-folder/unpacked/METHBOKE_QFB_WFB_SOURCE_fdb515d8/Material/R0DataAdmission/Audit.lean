import R0DataAdmission.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology Interval

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.smooth_datum_representative_ne_zero
example : ∀ {a : Field} (ha : SmoothSigmaZero a) (ha0 : a ≠ 0),
    criticalL2Representative a ≠ 0 :=
  @MethbokeAddon.WeakFouriermanB.smooth_datum_representative_ne_zero

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.D_Q_subset_R_nu
example : ∀ (ν : ℝ) (hν : 0 < ν),
    D_Q ν ⊆ R_nu ν :=
  @MethbokeAddon.WeakFouriermanB.D_Q_subset_R_nu

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_representative_ne_zero"
#check @MethbokeAddon.WeakFouriermanB.smooth_datum_representative_ne_zero
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.smooth_datum_representative_ne_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_representative_ne_zero"
#print axioms MethbokeAddon.WeakFouriermanB.smooth_datum_representative_ne_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.smooth_datum_representative_ne_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.D_Q_subset_R_nu"
#check @MethbokeAddon.WeakFouriermanB.D_Q_subset_R_nu
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.D_Q_subset_R_nu"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.D_Q_subset_R_nu"
#print axioms MethbokeAddon.WeakFouriermanB.D_Q_subset_R_nu
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.D_Q_subset_R_nu"

