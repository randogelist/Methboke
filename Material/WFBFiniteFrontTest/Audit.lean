import WFBFiniteFrontTest.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology Interval

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_contDiff
example : ∀ (c : ℝ) (b : ContDiffBump (0 : ℝ)),
    ContDiff ℝ ∞ (finiteFrontTimeClamp c b) :=
  @MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_contDiff

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_mem_Ioo
example : ∀ {c T : ℝ} (b : ContDiffBump (0 : ℝ))
    (hc : c ∈ Ioo (0 : ℝ) T) (houter : b.rOut < T)
    (r : ℝ) (hr : 0 < r),
    finiteFrontTimeClamp c b r ∈ Ioo (0 : ℝ) T :=
  @MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_mem_Ioo

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_through
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : LocalPhysicalNSEFront ν T a u p)
    (t : ℝ) (ht0 : 0 < t) (htT : t < T),
    ∃ φ : Velocity, CriticalPositiveSolenoidalTest φ ∧
      (∀ r ∈ Ioc (0 : ℝ) t, φ =ᶠ[𝓝 r] u) ∧ φ =ᶠ[𝓝 (0 : ℝ)] u :=
  @MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_through

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_on_compact
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : LocalPhysicalNSEFront ν T a u p)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t < T),
    ∃ φ : Velocity, CriticalPositiveSolenoidalTest φ ∧
      ∀ r ∈ Icc s t, φ =ᶠ[𝓝 r] u :=
  @MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_on_compact

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.local_test_timeDerivative_eq_of_eventuallyEq
example : ∀ {φ u : Velocity} {r : ℝ} (h : φ =ᶠ[𝓝 r] u) (x : Vec),
    timeDerivative φ r x = timeDerivative u r x :=
  @MethbokeAddon.WeakFouriermanB.local_test_timeDerivative_eq_of_eventuallyEq

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_contDiff"
#check @MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_contDiff
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_contDiff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_contDiff"
#print axioms MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_contDiff
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_contDiff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_mem_Ioo"
#check @MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_mem_Ioo
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_mem_Ioo"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_mem_Ioo"
#print axioms MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_mem_Ioo
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.finiteFrontTimeClamp_mem_Ioo"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_through"
#check @MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_through
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_through"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_through"
#print axioms MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_through
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_through"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_on_compact"
#check @MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_on_compact
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_on_compact"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_on_compact"
#print axioms MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_on_compact
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_front_exists_global_test_on_compact"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_test_timeDerivative_eq_of_eventuallyEq"
#check @MethbokeAddon.WeakFouriermanB.local_test_timeDerivative_eq_of_eventuallyEq
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_test_timeDerivative_eq_of_eventuallyEq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_test_timeDerivative_eq_of_eventuallyEq"
#print axioms MethbokeAddon.WeakFouriermanB.local_test_timeDerivative_eq_of_eventuallyEq
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_test_timeDerivative_eq_of_eventuallyEq"

