import QFAWeightedBudgetAllWindows.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory MethbokeAddon.QuasiFeffermanA
open scoped BigOperators

noncomputable section

/- Independent consumer of the actual velocity/weak-gradient statement,
with the finite horizon universally quantified after physical membership. -/
example {ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 < ν) :
    ∀ T : ℝ, 0 ≤ T →
      Integrable (fun t => ‖u t‖ ^ 2 * (∑ j : Fin 3, ‖G t j‖ ^ 2))
          (volume.restrict (Ioo (0 : ℝ) T)) ∧
        (∫ t in Ioo (0 : ℝ) T, ‖u t‖ ^ 2 * (∑ j : Fin 3, ‖G t j‖ ^ 2)) ≤
          ‖a‖ ^ 4 / (4 * ν) := by
  intro T hT
  exact h.energy_product_budget_Ioo_nonneg hν hT

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.energy_product_budget_Ioo_nonneg"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.energy_product_budget_Ioo_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.energy_product_budget_Ioo_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.energy_product_budget_Ioo_nonneg"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.energy_product_budget_Ioo_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.energy_product_budget_Ioo_nonneg"
