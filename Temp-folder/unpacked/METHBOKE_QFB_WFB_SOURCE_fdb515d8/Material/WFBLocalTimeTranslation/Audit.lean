import WFBLocalTimeTranslation.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB
open scoped ContDiff Topology
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_time_hasDerivAt
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (x : Vec),
    HasDerivAt (fun r : ℝ => u r x) (timeDerivative u t x) t :=
  @MethbokeAddon.WeakFouriermanB.initial_front_time_hasDerivAt

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_translate
example : ∀ (ν T s : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hs : 0 ≤ s)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) (T - s)) (x : Vec),
    timeDerivative (fun r => u (s + r)) t x = timeDerivative u (s + t) x :=
  @MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_translate

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_time_translate
example : ∀ (ν T s : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hs : 0 ≤ s),
    InitialClassicalFront ν (T - s) (u s)
      (fun t => u (s + t)) (fun t => p (s + t)) :=
  @MethbokeAddon.WeakFouriermanB.initial_front_time_translate

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_shift_back
example : ∀ (ν T s : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hs : 0 ≤ s)
    (t : ℝ) (ht : t ∈ Ioo s (s + T)) (x : Vec),
    timeDerivative (fun r => u (r - s)) t x = timeDerivative u (t - s) x :=
  @MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_shift_back

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_shift_back_equation
example : ∀ (ν T s : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hs : 0 ≤ s)
    (t : ℝ) (ht : t ∈ Ioo s (s + T)) (x : Vec),
    timeDerivative (fun r => u (r - s)) t x + convection (u (t - s)) x +
      SingularClosure.gradient (p (t - s)) x = ν • laplacian (u (t - s)) x :=
  @MethbokeAddon.WeakFouriermanB.initial_front_shift_back_equation

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_time_hasDerivAt"
#check @MethbokeAddon.WeakFouriermanB.initial_front_time_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_time_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_time_hasDerivAt"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_time_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_time_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_translate"
#check @MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_translate
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_translate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_translate"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_translate
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_translate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_time_translate"
#check @MethbokeAddon.WeakFouriermanB.initial_front_time_translate
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_time_translate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_time_translate"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_time_translate
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_time_translate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_shift_back"
#check @MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_shift_back
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_shift_back"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_shift_back"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_shift_back
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_timeDerivative_shift_back"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_shift_back_equation"
#check @MethbokeAddon.WeakFouriermanB.initial_front_shift_back_equation
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_shift_back_equation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_shift_back_equation"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_shift_back_equation
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_shift_back_equation"
