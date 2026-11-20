import WFBPhysicalBudgetContinuation.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped ContDiff ENNReal Interval Topology
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_dissipation_square_integrable_of_fourier_budget
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p)
    (hbudget : FourierBudgetFinite (fun t => datumFourierCoeff (u t)) T),
    Integrable (fun t => physicalDissipation (u t) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) T)) :=
  @MethbokeAddon.WeakFouriermanB.initial_front_dissipation_square_integrable_of_fourier_budget

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_dissipation_square
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hT : 0 < T) (H : InitialClassicalFront ν T a u p)
    (hD : Integrable (fun t => physicalDissipation (u t) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) T))),
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico (0 : ℝ) T,
      physicalDissipation (u t) +
        ν * (∫ s in (0 : ℝ)..t, physicalLaplacianSquare (u s)) ≤ B :=
  @MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_dissipation_square

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_fourier_budget
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hT : 0 < T) (H : InitialClassicalFront ν T a u p)
    (hbudget : FourierBudgetFinite (fun t => datumFourierCoeff (u t)) T),
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico (0 : ℝ) T,
      physicalDissipation (u t) +
        ν * (∫ s in (0 : ℝ)..t, physicalLaplacianSquare (u s)) ≤ B :=
  @MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_fourier_budget

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_dissipation_square
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hT : 0 < T) (H : InitialClassicalFront ν T a u p)
    (hD : Integrable (fun t => physicalDissipation (u t) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) T))),
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Ico (0 : ℝ) T, physicalH1Square (u t) ≤ R :=
  @MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_dissipation_square

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_fourier_budget
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hT : 0 < T) (H : InitialClassicalFront ν T a u p)
    (hbudget : FourierBudgetFinite (fun t => datumFourierCoeff (u t)) T),
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Ico (0 : ℝ) T, physicalH1Square (u t) ≤ R :=
  @MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_fourier_budget

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.maximal_front_uniform_H1_before_budget_cap
example : ∀ (ν cutoff : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (H : MaximalClassicalFront ν a u p Tmax)
    (hbudget : MaximalFourierBudgetFinite u Tmax cutoff),
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t : ℝ, 0 ≤ t →
      ENNReal.ofReal t < min Tmax (ENNReal.ofReal cutoff) →
      physicalH1Square (u t) ≤ R :=
  @MethbokeAddon.WeakFouriermanB.maximal_front_uniform_H1_before_budget_cap

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_dissipation_square_integrable_of_fourier_budget"
#check @MethbokeAddon.WeakFouriermanB.initial_front_dissipation_square_integrable_of_fourier_budget
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_dissipation_square_integrable_of_fourier_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_dissipation_square_integrable_of_fourier_budget"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_dissipation_square_integrable_of_fourier_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_dissipation_square_integrable_of_fourier_budget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_dissipation_square"
#check @MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_dissipation_square
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_dissipation_square"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_dissipation_square"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_dissipation_square
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_dissipation_square"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_fourier_budget"
#check @MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_fourier_budget
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_fourier_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_fourier_budget"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_fourier_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_enstrophy_accumulation_of_fourier_budget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_dissipation_square"
#check @MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_dissipation_square
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_dissipation_square"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_dissipation_square"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_dissipation_square
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_dissipation_square"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_fourier_budget"
#check @MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_fourier_budget
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_fourier_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_fourier_budget"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_fourier_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_uniform_H1_of_fourier_budget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_front_uniform_H1_before_budget_cap"
#check @MethbokeAddon.WeakFouriermanB.maximal_front_uniform_H1_before_budget_cap
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.maximal_front_uniform_H1_before_budget_cap"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_front_uniform_H1_before_budget_cap"
#print axioms MethbokeAddon.WeakFouriermanB.maximal_front_uniform_H1_before_budget_cap
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.maximal_front_uniform_H1_before_budget_cap"
