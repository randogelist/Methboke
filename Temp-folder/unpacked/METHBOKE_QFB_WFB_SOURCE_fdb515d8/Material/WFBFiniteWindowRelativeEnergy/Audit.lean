import WFBFiniteWindowRelativeEnergy.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology Interval

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.finite_window_smooth_nse_energy_identity
example : ∀ (ν : ℝ) (hν : 0 < ν) (u : Velocity) (p : Pressure)
    (hu : CriticalPositiveSolenoidalTest u)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (hp : ∀ r ∈ Icc s t, ContDiff ℝ ∞ (p r))
    (hpp : ∀ r ∈ Icc s t, SpatialPeriodic (p r))
    (hNSE : ∀ r ∈ Icc s t, ∀ x : Vec,
      timeDerivative u r x + convection (u r) x + SingularClosure.gradient (p r) x =
        ν • laplacian (u r) x),
    IntervalIntegrable (fun r => physicalDissipation (u r)) volume s t ∧
      physicalEnergy (u t) + 2 * ν * (∫ r in s..t, physicalDissipation (u r)) =
        physicalEnergy (u s) :=
  @MethbokeAddon.WeakFouriermanB.finite_window_smooth_nse_energy_identity

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_raw
example : ∀ (ν : ℝ) (hν : 0 < ν) (a₀ : CriticalPhysicalL2)
    (v u : Velocity) (G : ℝ → Vec → (Vec →L[ℝ] Vec)) (p : Pressure)
    (hv : CriticalLerayHopf ν a₀ v G)
    (hu : CriticalPositiveSolenoidalTest u)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (hp : ∀ r ∈ Icc s t, ContDiff ℝ ∞ (p r))
    (hpp : ∀ r ∈ Icc s t, SpatialPeriodic (p r))
    (hNSE : ∀ r ∈ Icc s t, ∀ x : Vec,
      timeDerivative u r x + convection (u r) x + SingularClosure.gradient (p r) x =
        ν • laplacian (u r) x)
    (henergy : physicalEnergy (v t) +
      2 * ν * (∫ r in s..t, criticalGradientEnergy (G r)) ≤ physicalEnergy (v s)),
    IntervalIntegrable (fun r => criticalGradientEnergy (G r - fderiv ℝ (u r))) volume s t ∧
    IntervalIntegrable (fun r => criticalWeakTransport (v r) (u r) -
      physicalFieldInner (v r) (convection (u r))) volume s t ∧
    physicalEnergy (v t - u t) +
      2 * ν * (∫ r in s..t, criticalGradientEnergy (G r - fderiv ℝ (u r))) ≤
      physicalEnergy (v s - u s) - 2 * (∫ r in s..t,
        criticalWeakTransport (v r) (u r) - physicalFieldInner (v r) (convection (u r))) :=
  @MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_raw

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_transport
example : ∀ (ν : ℝ) (hν : 0 < ν) (a₀ : CriticalPhysicalL2)
    (v u : Velocity) (G : ℝ → Vec → (Vec →L[ℝ] Vec)) (p : Pressure)
    (hv : CriticalLerayHopf ν a₀ v G)
    (hu : CriticalPositiveSolenoidalTest u)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (hp : ∀ r ∈ Icc s t, ContDiff ℝ ∞ (p r))
    (hpp : ∀ r ∈ Icc s t, SpatialPeriodic (p r))
    (hNSE : ∀ r ∈ Icc s t, ∀ x : Vec,
      timeDerivative u r x + convection (u r) x + SingularClosure.gradient (p r) x =
        ν • laplacian (u r) x)
    (henergy : physicalEnergy (v t) +
      2 * ν * (∫ r in s..t, criticalGradientEnergy (G r)) ≤ physicalEnergy (v s)),
    IntervalIntegrable (fun r => criticalGradientEnergy (G r - fderiv ℝ (u r))) volume s t ∧
    IntervalIntegrable (fun r => criticalRoughTransport (v r - u r)
      (G r - fderiv ℝ (u r)) (u r)) volume s t ∧
    physicalEnergy (v t - u t) +
      2 * ν * (∫ r in s..t, criticalGradientEnergy (G r - fderiv ℝ (u r))) ≤
      physicalEnergy (v s - u s) + 2 * (∫ r in s..t,
        criticalRoughTransport (v r - u r) (G r - fderiv ℝ (u r)) (u r)) :=
  @MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_transport

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.finite_window_smooth_nse_energy_identity"
#check @MethbokeAddon.WeakFouriermanB.finite_window_smooth_nse_energy_identity
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.finite_window_smooth_nse_energy_identity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.finite_window_smooth_nse_energy_identity"
#print axioms MethbokeAddon.WeakFouriermanB.finite_window_smooth_nse_energy_identity
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.finite_window_smooth_nse_energy_identity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_raw"
#check @MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_raw
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_raw"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_raw"
#print axioms MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_raw
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_raw"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_transport"
#check @MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_transport
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_transport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_transport"
#print axioms MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_transport
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.finite_window_lh_smooth_relative_energy_transport"

