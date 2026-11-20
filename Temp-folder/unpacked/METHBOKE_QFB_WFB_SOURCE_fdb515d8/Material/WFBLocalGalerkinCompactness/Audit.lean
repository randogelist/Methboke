import WFBLocalGalerkinCompactness.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory Filter Metric SingularClosure
open scoped Topology BoundedContinuousFunction Interval
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_canonical_galerkin_H0_uniform_subsequence
example : ∀ (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T)
    (S : ℝ) (hS : 0 ≤ S)
    (hH2 : ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ S),
    ∃ u : C(Icc (0 : ℝ) T, TorusSobolev 0), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformly
        (fun n (t : Icc (0 : ℝ) T) =>
          (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t.val)
        u atTop :=
  @MethbokeAddon.WeakFouriermanB.local_canonical_galerkin_H0_uniform_subsequence

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_canonical_galerkin_H0_uniform_subsequence"
#check @MethbokeAddon.WeakFouriermanB.local_canonical_galerkin_H0_uniform_subsequence
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_canonical_galerkin_H0_uniform_subsequence"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_canonical_galerkin_H0_uniform_subsequence"
#print axioms MethbokeAddon.WeakFouriermanB.local_canonical_galerkin_H0_uniform_subsequence
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_canonical_galerkin_H0_uniform_subsequence"
