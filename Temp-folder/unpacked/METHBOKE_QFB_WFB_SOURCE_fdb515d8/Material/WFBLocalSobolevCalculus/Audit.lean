import WFBLocalSobolevCalculus.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped ContDiff Topology Interval
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_sobolev_hasDerivWithinAt_of_coefficient_integral
example : ∀ (s : ℕ) (T : ℝ) (hT : 0 ≤ T) (u r : ℝ → TorusSobolev s)
    (hr : ContinuousOn r (Icc (0 : ℝ) T))
    (hcoeff : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Frequency, ∀ i : Fin 3,
      (u t).val k i = (u 0).val k i + ∫ z in (0 : ℝ)..t, (r z).val k i)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T),
    HasDerivWithinAt u (r t) (Icc (0 : ℝ) T) t :=
  @MethbokeAddon.WeakFouriermanB.local_sobolev_hasDerivWithinAt_of_coefficient_integral

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_sobolevScale_contDiffOn_nat
example : ∀ (T : ℝ) (hT : 0 < T)
    (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (F : ∀ m : ℕ, TorusSobolev (m + 2) → TorusSobolev m)
    (hU : ∀ m : ℕ, ContinuousOn (U m) (Icc (0 : ℝ) T))
    (hF : ∀ m : ℕ, ContDiff ℝ ∞ (F m))
    (hderiv : ∀ (m : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (U m) (F m (U (m + 2) t)) (Icc (0 : ℝ) T) t)
    (n m : ℕ),
    ContDiffOn ℝ n (U m) (Icc (0 : ℝ) T) :=
  @MethbokeAddon.WeakFouriermanB.local_sobolevScale_contDiffOn_nat

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_sobolev_scale_time_smooth
example : ∀ (T : ℝ) (hT : 0 < T)
    (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (F : ∀ m : ℕ, TorusSobolev (m + 2) → TorusSobolev m)
    (hU : ∀ m : ℕ, ContinuousOn (U m) (Icc (0 : ℝ) T))
    (hF : ∀ m : ℕ, ContDiff ℝ ∞ (F m))
    (hderiv : ∀ (m : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (U m) (F m (U (m + 2) t)) (Icc (0 : ℝ) T) t),
    ∀ m : ℕ, ContDiffOn ℝ ∞ (U m) (Icc (0 : ℝ) T) :=
  @MethbokeAddon.WeakFouriermanB.local_sobolev_scale_time_smooth

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_sobolev_curves_joint_spacetime_smooth
example : ∀ (T : ℝ) (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (hU : ∀ s : ℕ, ContDiffOn ℝ ∞ (U s) (Icc (0 : ℝ) T))
    (hcoeff : ∀ (s : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      (U s t).val = (U 0 t).val),
    ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => smoothFourierSynthesis (U 0 z.1).val z.2)
      (initialFrontSpacetime T) :=
  @MethbokeAddon.WeakFouriermanB.local_sobolev_curves_joint_spacetime_smooth

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_contDiffOn
example : ∀ (T : ℝ) (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (hU : ∀ s : ℕ, ContDiffOn ℝ ∞ (U s) (Icc (0 : ℝ) T)) (s : ℕ),
    ContDiffOn ℝ ∞ (sobolevTransportPressureCurve U s) (Icc (0 : ℝ) T) :=
  @MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_contDiffOn

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_coeff
example : ∀ (T : ℝ) (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (hcoeff : ∀ (s : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      (U s t).val = (U 0 t).val)
    (s : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T),
    (sobolevTransportPressureCurve U s t).val =
      pressureVectorCoeff (fullTransportCoefficients (U 0 t)) :=
  @MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_coeff

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.local_sobolev_pressure_joint_smooth
example : ∀ (T : ℝ) (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (hU : ∀ s : ℕ, ContDiffOn ℝ ∞ (U s) (Icc (0 : ℝ) T))
    (hcoeff : ∀ (s : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      (U s t).val = (U 0 t).val),
    ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => fullTransportPressure (U 0 z.1) z.2)
      (initialFrontSpacetime T) :=
  @MethbokeAddon.WeakFouriermanB.local_sobolev_pressure_joint_smooth

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.state_all_mem
example : ∀ {ν T : ℝ} (L : LocalSobolevFlow ν T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (s : ℕ),
    Memℓp (sobolevWeightedCoeff s (L.state 0 t).val) 2 :=
  @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.state_all_mem

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.rhs_coeff
example : ∀ {ν T : ℝ} (L : LocalSobolevFlow ν T) (r : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T),
    (fourierSobolevRhs ν r (L.state (r + 2) t)).val = fullFourierRhs ν (L.state 0 t) :=
  @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.rhs_coeff

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.time_smooth
example : ∀ {ν T : ℝ} (L : LocalSobolevFlow ν T) (hT : 0 < T),
    ∀ r : ℕ, ContDiffOn ℝ ∞ (L.state r) (Icc (0 : ℝ) T) :=
  @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.time_smooth

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_spacetime_smooth
example : ∀ {ν T : ℝ} (L : LocalSobolevFlow ν T) (hT : 0 < T),
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => L.velocity z.1 z.2) (initialFrontSpacetime T) :=
  @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_spacetime_smooth

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.pressure_spacetime_smooth
example : ∀ {ν T : ℝ} (L : LocalSobolevFlow ν T) (hT : 0 < T),
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => L.pressure z.1 z.2) (initialFrontSpacetime T) :=
  @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.pressure_spacetime_smooth

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_timeDerivative
example : ∀ {ν T : ℝ} (L : LocalSobolevFlow ν T) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T),
    timeDerivative L.velocity t = smoothFourierSynthesis (fullFourierRhs ν (L.state 0 t)) :=
  @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_timeDerivative

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.physical_equation
example : ∀ {ν T : ℝ} (L : LocalSobolevFlow ν T) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) (x : Vec),
    timeDerivative L.velocity t x + convection (L.velocity t) x +
      SingularClosure.gradient (L.pressure t) x = ν • laplacian (L.velocity t) x :=
  @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.physical_equation

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_smoothSigmaZero
example : ∀ {ν T : ℝ} (L : LocalSobolevFlow ν T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T),
    SmoothSigmaZero (L.velocity t) :=
  @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_smoothSigmaZero

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initial_eq
example : ∀ {ν T : ℝ} (L : LocalSobolevFlow ν T) (hT : 0 ≤ T)
    (a : Field) (ha : SmoothSigmaZero a)
    (hinitial : (L.state 0 0).val = datumFourierCoeff a),
    L.velocity 0 = a :=
  @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initial_eq

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initialClassicalFront
example : ∀ {ν T : ℝ} (L : LocalSobolevFlow ν T) (hT : 0 < T)
    (a : Field) (ha : SmoothSigmaZero a)
    (hinitial : (L.state 0 0).val = datumFourierCoeff a),
    InitialClassicalFront ν T a L.velocity L.pressure :=
  @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initialClassicalFront

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolev_hasDerivWithinAt_of_coefficient_integral"
#check @MethbokeAddon.WeakFouriermanB.local_sobolev_hasDerivWithinAt_of_coefficient_integral
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_sobolev_hasDerivWithinAt_of_coefficient_integral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolev_hasDerivWithinAt_of_coefficient_integral"
#print axioms MethbokeAddon.WeakFouriermanB.local_sobolev_hasDerivWithinAt_of_coefficient_integral
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_sobolev_hasDerivWithinAt_of_coefficient_integral"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolevScale_contDiffOn_nat"
#check @MethbokeAddon.WeakFouriermanB.local_sobolevScale_contDiffOn_nat
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_sobolevScale_contDiffOn_nat"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolevScale_contDiffOn_nat"
#print axioms MethbokeAddon.WeakFouriermanB.local_sobolevScale_contDiffOn_nat
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_sobolevScale_contDiffOn_nat"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolev_scale_time_smooth"
#check @MethbokeAddon.WeakFouriermanB.local_sobolev_scale_time_smooth
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_sobolev_scale_time_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolev_scale_time_smooth"
#print axioms MethbokeAddon.WeakFouriermanB.local_sobolev_scale_time_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_sobolev_scale_time_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolev_curves_joint_spacetime_smooth"
#check @MethbokeAddon.WeakFouriermanB.local_sobolev_curves_joint_spacetime_smooth
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_sobolev_curves_joint_spacetime_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolev_curves_joint_spacetime_smooth"
#print axioms MethbokeAddon.WeakFouriermanB.local_sobolev_curves_joint_spacetime_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_sobolev_curves_joint_spacetime_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_contDiffOn"
#check @MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_contDiffOn"
#print axioms MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_coeff"
#check @MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_coeff
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_coeff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_coeff"
#print axioms MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_coeff
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_sobolevTransportPressureCurve_coeff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolev_pressure_joint_smooth"
#check @MethbokeAddon.WeakFouriermanB.local_sobolev_pressure_joint_smooth
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_sobolev_pressure_joint_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_sobolev_pressure_joint_smooth"
#print axioms MethbokeAddon.WeakFouriermanB.local_sobolev_pressure_joint_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_sobolev_pressure_joint_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.state_all_mem"
#check @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.state_all_mem
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.state_all_mem"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.state_all_mem"
#print axioms MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.state_all_mem
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.state_all_mem"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.rhs_coeff"
#check @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.rhs_coeff
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.rhs_coeff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.rhs_coeff"
#print axioms MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.rhs_coeff
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.rhs_coeff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.time_smooth"
#check @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.time_smooth
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.time_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.time_smooth"
#print axioms MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.time_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.time_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_spacetime_smooth"
#check @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_spacetime_smooth
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_spacetime_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_spacetime_smooth"
#print axioms MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_spacetime_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_spacetime_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.pressure_spacetime_smooth"
#check @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.pressure_spacetime_smooth
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.pressure_spacetime_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.pressure_spacetime_smooth"
#print axioms MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.pressure_spacetime_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.pressure_spacetime_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_timeDerivative"
#check @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_timeDerivative
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_timeDerivative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_timeDerivative"
#print axioms MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_timeDerivative
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_timeDerivative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.physical_equation"
#check @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.physical_equation
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.physical_equation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.physical_equation"
#print axioms MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.physical_equation
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.physical_equation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_smoothSigmaZero"
#check @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_smoothSigmaZero
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_smoothSigmaZero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_smoothSigmaZero"
#print axioms MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_smoothSigmaZero
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.velocity_smoothSigmaZero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initial_eq"
#check @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initial_eq
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initial_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initial_eq"
#print axioms MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initial_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initial_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initialClassicalFront"
#check @MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initialClassicalFront
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initialClassicalFront"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initialClassicalFront"
#print axioms MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initialClassicalFront
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.LocalSobolevFlow.initialClassicalFront"
