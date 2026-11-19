import WFBFiniteWindowSerrinComparison.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology Interval

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.finite_window_leray_hopf_serrin_comparison
example : ∀ (ν : ℝ) (hν : 0 < ν) (a₀ : CriticalPhysicalL2)
    (v u : Velocity) (G : ℝ → Vec → (Vec →L[ℝ] Vec)) (p : Pressure)
    (hv : CriticalLerayHopf ν a₀ v G)
    (hu : CriticalPositiveSolenoidalTest u)
    (T : ℝ) (hT : 0 < T)
    (hp : ∀ r ∈ Ioc (0 : ℝ) T, ContDiff ℝ ∞ (p r))
    (hpp : ∀ r ∈ Ioc (0 : ℝ) T, SpatialPeriodic (p r))
    (hNSE : ∀ r ∈ Ioc (0 : ℝ) T, ∀ x : Vec,
      timeDerivative u r x + convection (u r) x + SingularClosure.gradient (p r) x =
        ν • laplacian (u r) x)
    (hu_trace : Tendsto
      (fun t => eLpNorm (u t - (a₀ : Vec → Vec)) 2 (volume.restrict unitCube))
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hSerrin : MemLp (fun t => criticalSpatialNorm 6 (u t)) 4
      (volume.restrict (Ioc (0 : ℝ) T))),
    ∀ t ∈ Ioc (0 : ℝ) T, v t =ᵐ[volume.restrict unitCube] u t :=
  @MethbokeAddon.WeakFouriermanB.finite_window_leray_hopf_serrin_comparison

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.finite_window_leray_hopf_serrin_comparison"
#check @MethbokeAddon.WeakFouriermanB.finite_window_leray_hopf_serrin_comparison
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.finite_window_leray_hopf_serrin_comparison"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.finite_window_leray_hopf_serrin_comparison"
#print axioms MethbokeAddon.WeakFouriermanB.finite_window_leray_hopf_serrin_comparison
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.finite_window_leray_hopf_serrin_comparison"

