import WFBLocalGalerkinRegularity.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped Interval
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_accumulation
example : ∀ (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T)
    (S : ℝ) (hS : 0 ≤ S)
    (hH2 : ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ S)
    (m : ℕ),
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ t ∈ Icc (0 : ℝ) T,
        ‖g.sobolevState m t‖ ^ 2 +
          ν * (∫ s in (0 : ℝ)..t, ‖g.sobolevState (m + 1) s‖ ^ 2) ≤ B :=
  @MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_accumulation

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_pointwise
example : ∀ (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T)
    (S : ℝ) (hS : 0 ≤ S)
    (hH2 : ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ S)
    (m : ℕ),
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ t ∈ Icc (0 : ℝ) T, ‖g.sobolevState m t‖ ^ 2 ≤ B :=
  @MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_pointwise

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_rhs
example : ∀ (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T)
    (S : ℝ) (hS : 0 ≤ S)
    (hH2 : ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ S)
    (m : ℕ),
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ t ∈ Icc (0 : ℝ) T, ‖g.rhsSobolev m t‖ ^ 2 ≤ B :=
  @MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_rhs

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_time_modulus
example : ∀ (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T)
    (S : ℝ) (hS : 0 ≤ S)
    (hH2 : ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ S)
    (m : ℕ),
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
        ‖g.sobolevState m t - g.sobolevState m s‖ ^ 2 ≤ B * |t - s| :=
  @MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_time_modulus

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_accumulation"
#check @MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_accumulation
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_accumulation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_accumulation"
#print axioms MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_accumulation
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_accumulation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_pointwise"
#check @MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_pointwise
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_pointwise"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_pointwise"
#print axioms MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_pointwise
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_pointwise"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_rhs"
#check @MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_rhs
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_rhs"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_rhs"
#print axioms MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_rhs
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_rhs"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_time_modulus"
#check @MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_time_modulus
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_time_modulus"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_time_modulus"
#print axioms MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_time_modulus
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_galerkin_high_order_time_modulus"
