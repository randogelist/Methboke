import WFBFiniteWindowCrossIdentity.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology Interval

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.finite_window_weak_classical_cross_identity
example : ∀ (ν : ℝ) (v φ : Velocity) (p : Pressure)
    (hv : CriticalIntegratedWeakMomentum ν v)
    (hφ : CriticalPositiveSolenoidalTest φ)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (hp : ∀ r ∈ Icc s t, ContDiff ℝ ∞ (p r))
    (hpp : ∀ r ∈ Icc s t, SpatialPeriodic (p r))
    (hNSE : ∀ r ∈ Icc s t, ∀ x : Vec,
      timeDerivative φ r x + convection (φ r) x + SingularClosure.gradient (p r) x =
        ν • laplacian (φ r) x),
    IntervalIntegrable (fun r =>
      2 * ν * physicalFieldInner (v r) (laplacian (φ r)) -
        physicalFieldInner (v r) (convection (φ r)) + criticalWeakTransport (v r) (φ r))
      volume s t ∧
    physicalFieldInner (v t) (φ t) - physicalFieldInner (v s) (φ s) =
      ∫ r in s..t,
        2 * ν * physicalFieldInner (v r) (laplacian (φ r)) -
          physicalFieldInner (v r) (convection (φ r)) + criticalWeakTransport (v r) (φ r) :=
  @MethbokeAddon.WeakFouriermanB.finite_window_weak_classical_cross_identity

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.finite_window_weak_classical_cross_identity"
#check @MethbokeAddon.WeakFouriermanB.finite_window_weak_classical_cross_identity
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.finite_window_weak_classical_cross_identity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.finite_window_weak_classical_cross_identity"
#print axioms MethbokeAddon.WeakFouriermanB.finite_window_weak_classical_cross_identity
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.finite_window_weak_classical_cross_identity"

