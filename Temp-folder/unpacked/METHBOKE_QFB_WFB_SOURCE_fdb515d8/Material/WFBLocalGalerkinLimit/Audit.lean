import WFBLocalGalerkinLimit.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped Topology Interval
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_galerkin_limit
example : ∀ (ν : ℝ) (a : Field) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n : ℕ, GalerkinSolution ν a (φ n + 1))
    (T : ℝ) (hT : 0 < T)
    (u : ℝ → TorusSobolev 0) (hu : ContinuousOn u (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      u atTop (Icc (0 : ℝ) T))
    (hbound : ∀ s : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T → ‖(g n).sobolevState s t‖ ≤ B),
    ∃ L : LocalSobolevFlow ν T, ∀ t ∈ Icc (0 : ℝ) T, L.state 0 t = u t :=
  @MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_galerkin_limit

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_uniform_H2
example : ∀ (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) (S : ℝ) (hS : 0 ≤ S)
    (hH2 : ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ S),
    ∃ L : LocalSobolevFlow ν T, (L.state 0 0).val = datumFourierCoeff a :=
  @MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_uniform_H2

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_galerkin_limit"
#check @MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_galerkin_limit
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_galerkin_limit"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_galerkin_limit"
#print axioms MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_galerkin_limit
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_galerkin_limit"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_uniform_H2"
#check @MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_uniform_H2
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_uniform_H2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_uniform_H2"
#print axioms MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_uniform_H2
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_sobolev_flow_of_uniform_H2"
