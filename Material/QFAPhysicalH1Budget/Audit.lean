import QFAPhysicalH1Budget.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Interval ENNReal Topology

namespace QFAPhysicalH1Budget.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA

-- Both observables are literally the norms of the actual graph coordinates.
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example (u : PhysicalH1) :
    physicalH1Energy u = ‖physicalH1Velocity u‖ ^ 2 := rfl
example (u : PhysicalH1) :
    physicalH1Enstrophy u = ∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2 := rfl
example (Y : ℝ → ℝ) (b : ℝ) :
    stoppedSquareBudget Y b =
      ∫⁻ t in Ioo (0 : ℝ) b, ENNReal.ofReal ((Y t) ^ 2) := rfl

example (u : PhysicalH1) : 0 ≤ ‖physicalH1Velocity u‖ ^ 2 :=
  physicalH1Energy_nonneg u
example (u : PhysicalH1) : 0 ≤ ∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2 :=
  physicalH1Enstrophy_nonneg u
example : Continuous (fun u : PhysicalH1 => ‖physicalH1Velocity u‖ ^ 2) :=
  physicalH1Energy_continuous
example : Continuous
    (fun u : PhysicalH1 => ∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2) :=
  physicalH1Enstrophy_continuous

example (u : PhysicalH1) :
    ‖u‖ ^ 2 = ‖physicalH1Velocity u‖ ^ 2 +
      ∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2 :=
  physicalH1_norm_sq_eq_energy_add_enstrophy u

example (u : PhysicalH1) : ‖physicalH1Velocity u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
  physicalH1Energy_le_norm_sq u
example (u : PhysicalH1) : (∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2) ≤ ‖u‖ ^ 2 :=
  physicalH1Enstrophy_le_norm_sq u

example (u : PhysicalH1) (E0 B : ℝ)
    (hE : ‖physicalH1Velocity u‖ ^ 2 ≤ E0)
    (hY : (∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2) ≤ B) :
    ‖u‖ ^ 2 ≤ E0 + B :=
  physicalH1_norm_sq_le_of_energy_enstrophy u hE hY

example (U : ℝ → PhysicalH1) (s : Set ℝ) (E0 B : ℝ)
    (hE : ∀ t ∈ s, ‖physicalH1Velocity (U t)‖ ^ 2 ≤ E0)
    (hY : ∀ t ∈ s, (∑ j : Fin 3, ‖physicalH1Gradient j (U t)‖ ^ 2) ≤ B) :
    ∀ t ∈ s, ‖U t‖ ^ 2 ≤ E0 + B :=
  physicalH1_path_norm_sq_le U s hE hY

-- Full closed-slab continuity is a visible hypothesis, not prefix continuity.
example (U : ℝ → PhysicalH1) (b : ℝ)
    (hU : ContinuousOn U (Icc (0 : ℝ) b)) :
    IntegrableOn
      (fun t => (∑ j : Fin 3, ‖physicalH1Gradient j (U t)‖ ^ 2) ^ 2)
      (Icc (0 : ℝ) b) volume :=
  physicalH1_enstrophy_sq_integrableOn_Icc U hU

example (U : ℝ → PhysicalH1) (b : ℝ)
    (hU : ContinuousOn U (Icc (0 : ℝ) b)) :
    (∫⁻ t in Ioo (0 : ℝ) b,
      ENNReal.ofReal ((∑ j : Fin 3, ‖physicalH1Gradient j (U t)‖ ^ 2) ^ 2)) =
      ENNReal.ofReal (∫ t in Ioo (0 : ℝ) b,
        (∑ j : Fin 3, ‖physicalH1Gradient j (U t)‖ ^ 2) ^ 2) :=
  physicalH1_stoppedSquareBudget_eq_integral U hU

example (U : ℝ → PhysicalH1) (b : ℝ)
    (hU : ContinuousOn U (Icc (0 : ℝ) b)) :
    (∫⁻ t in Ioo (0 : ℝ) b,
      ENNReal.ofReal ((∑ j : Fin 3, ‖physicalH1Gradient j (U t)‖ ^ 2) ^ 2)) ≠ ∞ :=
  physicalH1_stoppedSquareBudget_finite U hU

-- No energy law, cubic inequality, or full-budget finiteness is hidden.
example (U : ℝ → PhysicalH1) (κ b E0 : ℝ) (hκ : 0 ≤ κ)
    (hE : ∀ t ∈ Ico (0 : ℝ) b, physicalH1Energy (U t) ≤ E0)
    (hAC : ∀ R ∈ Ico (0 : ℝ) b,
      AbsolutelyContinuousOnInterval (fun t => physicalH1Enstrophy (U t)) 0 R)
    (hcubic : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) b),
      deriv (fun t => physicalH1Enstrophy (U t)) r ≤
        κ * (physicalH1Enstrophy (U r)) ^ 3)
    (hbudget : (∫⁻ t in Ioo (0 : ℝ) b,
      ENNReal.ofReal ((physicalH1Enstrophy (U t)) ^ 2)) ≠ ∞) :
    ∀ t ∈ Ico (0 : ℝ) b,
      ‖U t‖ ^ 2 ≤ E0 + physicalH1Enstrophy (U 0) * Real.exp
        (κ * (∫⁻ r in Ioo (0 : ℝ) b,
          ENNReal.ofReal ((physicalH1Enstrophy (U r)) ^ 2)).toReal) :=
  physicalH1_ac_cubic_uniform_norm_sq U hκ hE hAC hcubic hbudget

end QFAPhysicalH1Budget.ExpectedTypes

-- NAMED REPORTS: executed only by authorized external CI.
#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Energy"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Energy
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Energy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Energy"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Energy
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Energy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Energy_nonneg"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Energy_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Energy_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Energy_nonneg"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Energy_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Energy_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_nonneg"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_nonneg"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Energy_continuous"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Energy_continuous
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Energy_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Energy_continuous"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Energy_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Energy_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_continuous"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_continuous
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_continuous"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq_eq_energy_add_enstrophy"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq_eq_energy_add_enstrophy
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq_eq_energy_add_enstrophy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq_eq_energy_add_enstrophy"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq_eq_energy_add_enstrophy
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq_eq_energy_add_enstrophy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Energy_le_norm_sq"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Energy_le_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Energy_le_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Energy_le_norm_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Energy_le_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Energy_le_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_le_norm_sq"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_le_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_le_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_le_norm_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_le_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1Enstrophy_le_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq_le_of_energy_enstrophy"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq_le_of_energy_enstrophy
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq_le_of_energy_enstrophy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq_le_of_energy_enstrophy"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq_le_of_energy_enstrophy
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1_norm_sq_le_of_energy_enstrophy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_path_norm_sq_le"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1_path_norm_sq_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1_path_norm_sq_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_path_norm_sq_le"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1_path_norm_sq_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1_path_norm_sq_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_enstrophy_sq_integrableOn_Icc"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1_enstrophy_sq_integrableOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1_enstrophy_sq_integrableOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_enstrophy_sq_integrableOn_Icc"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1_enstrophy_sq_integrableOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1_enstrophy_sq_integrableOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_stoppedSquareBudget_eq_integral"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1_stoppedSquareBudget_eq_integral
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1_stoppedSquareBudget_eq_integral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_stoppedSquareBudget_eq_integral"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1_stoppedSquareBudget_eq_integral
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1_stoppedSquareBudget_eq_integral"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_stoppedSquareBudget_finite"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1_stoppedSquareBudget_finite
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1_stoppedSquareBudget_finite"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_stoppedSquareBudget_finite"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1_stoppedSquareBudget_finite
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1_stoppedSquareBudget_finite"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_ac_cubic_uniform_norm_sq"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1_ac_cubic_uniform_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1_ac_cubic_uniform_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1_ac_cubic_uniform_norm_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1_ac_cubic_uniform_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1_ac_cubic_uniform_norm_sq"

