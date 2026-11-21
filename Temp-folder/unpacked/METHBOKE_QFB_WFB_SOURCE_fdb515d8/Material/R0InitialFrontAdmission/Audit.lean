import R0InitialFrontAdmission.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology Interval

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.initial_front_smooth_slices
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p)
    (r : ℝ) (hr : r ∈ Ico (0 : ℝ) T),
    SmoothSigmaZero (u r) :=
  @MethbokeAddon.WeakFouriermanB.initial_front_smooth_slices

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.initial_front_initial_smooth
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hT : 0 < T),
    SmoothSigmaZero a :=
  @MethbokeAddon.WeakFouriermanB.initial_front_initial_smooth

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.initial_front_compact_cylinder_continuous
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p)
    (τ : ℝ) (hτT : τ < T),
    ContinuousOn (fun z : ℝ × Vec => u z.1 z.2)
      (Icc (0 : ℝ) τ ×ˢ unitCube) :=
  @MethbokeAddon.WeakFouriermanB.initial_front_compact_cylinder_continuous

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.initial_real_cube_integral_continuousOn_Icc
example : ∀ (T : ℝ) (F : ℝ → Vec → ℝ)
    (hF : ContinuousOn (fun z : ℝ × Vec => F z.1 z.2) (initialFrontSpacetime T))
    (τ : ℝ) (hτT : τ < T),
    ContinuousOn (fun r => ∫ x in unitCube, F r x) (Icc (0 : ℝ) τ) :=
  @MethbokeAddon.WeakFouriermanB.initial_real_cube_integral_continuousOn_Icc

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.initial_front_strong_initial_trace
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hT : 0 < T),
    Tendsto (fun r => eLpNorm (u r - a) 2 (volume.restrict unitCube))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  @MethbokeAddon.WeakFouriermanB.initial_front_strong_initial_trace

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.initial_front_to_local_physical
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hν : 0 < ν) (hT : 0 < T),
    LocalPhysicalNSEFront ν T a u p :=
  @MethbokeAddon.WeakFouriermanB.initial_front_to_local_physical

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.initial_front_compact_serrin
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hν : 0 < ν) (hT : 0 < T)
    (τ : ℝ) (hτ : 0 < τ) (hτT : τ < T),
    MemLp (fun r => criticalSpatialNorm 6 (u r)) 4
      (volume.restrict (Ioc (0 : ℝ) τ)) :=
  @MethbokeAddon.WeakFouriermanB.initial_front_compact_serrin

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.initial_front_leray_hopf_identification
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (v : Velocity) (G : WeakGradientTrajectory)
    (H : InitialClassicalFront ν T a u p) (hν : 0 < ν) (hT : 0 < T)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G),
    ∀ r ∈ Ioo (0 : ℝ) T, v r =ᵐ[volume.restrict unitCube] u r :=
  @MethbokeAddon.WeakFouriermanB.initial_front_leray_hopf_identification

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.initial_front_original_leray_hopf
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hν : 0 < ν) (hT : 0 < T),
    ∃ (v : Velocity) (G : WeakGradientTrajectory),
      CriticalLerayHopf ν (criticalL2Representative a) v G ∧
      v 0 =ᵐ[volume.restrict unitCube] a ∧
      ∀ r ∈ Ioo (0 : ℝ) T, v r =ᵐ[volume.restrict unitCube] u r :=
  @MethbokeAddon.WeakFouriermanB.initial_front_original_leray_hopf

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_smooth_slices"
#check @MethbokeAddon.WeakFouriermanB.initial_front_smooth_slices
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_smooth_slices"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_smooth_slices"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_smooth_slices
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_smooth_slices"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_initial_smooth"
#check @MethbokeAddon.WeakFouriermanB.initial_front_initial_smooth
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_initial_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_initial_smooth"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_initial_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_initial_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_compact_cylinder_continuous"
#check @MethbokeAddon.WeakFouriermanB.initial_front_compact_cylinder_continuous
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_compact_cylinder_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_compact_cylinder_continuous"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_compact_cylinder_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_compact_cylinder_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_real_cube_integral_continuousOn_Icc"
#check @MethbokeAddon.WeakFouriermanB.initial_real_cube_integral_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_real_cube_integral_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_real_cube_integral_continuousOn_Icc"
#print axioms MethbokeAddon.WeakFouriermanB.initial_real_cube_integral_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_real_cube_integral_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_strong_initial_trace"
#check @MethbokeAddon.WeakFouriermanB.initial_front_strong_initial_trace
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_strong_initial_trace"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_strong_initial_trace"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_strong_initial_trace
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_strong_initial_trace"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_to_local_physical"
#check @MethbokeAddon.WeakFouriermanB.initial_front_to_local_physical
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_to_local_physical"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_to_local_physical"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_to_local_physical
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_to_local_physical"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_compact_serrin"
#check @MethbokeAddon.WeakFouriermanB.initial_front_compact_serrin
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_compact_serrin"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_compact_serrin"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_compact_serrin
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_compact_serrin"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_leray_hopf_identification"
#check @MethbokeAddon.WeakFouriermanB.initial_front_leray_hopf_identification
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_leray_hopf_identification"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_leray_hopf_identification"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_leray_hopf_identification
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_leray_hopf_identification"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_original_leray_hopf"
#check @MethbokeAddon.WeakFouriermanB.initial_front_original_leray_hopf
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_original_leray_hopf"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_original_leray_hopf"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_original_leray_hopf
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_original_leray_hopf"

