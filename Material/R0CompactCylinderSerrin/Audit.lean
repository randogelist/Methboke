import R0CompactCylinderSerrin.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology Interval

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.compact_cylinder_velocity_bound
example : ∀ (u : Velocity) (τ : ℝ)
    (hcont : ContinuousOn (fun z : ℝ × Vec => u z.1 z.2)
      (Icc (0 : ℝ) τ ×ˢ unitCube)),
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ r ∈ Icc (0 : ℝ) τ, ∀ x ∈ unitCube, ‖u r x‖ ≤ M :=
  @MethbokeAddon.WeakFouriermanB.compact_cylinder_velocity_bound

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.spatialNorm_six_le_constant_of_cube_bound
example : ∀ (v : Field) (M : ℝ)
    (hbound : ∀ x ∈ unitCube, ‖v x‖ ≤ M),
    criticalSpatialNorm 6 v ≤ criticalSpatialNorm 6 (fun _ : Vec => M) :=
  @MethbokeAddon.WeakFouriermanB.spatialNorm_six_le_constant_of_cube_bound

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.compact_cylinder_spatialNorm_six_bound
example : ∀ (u : Velocity) (τ : ℝ)
    (hcont : ContinuousOn (fun z : ℝ × Vec => u z.1 z.2)
      (Icc (0 : ℝ) τ ×ˢ unitCube)),
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ r ∈ Icc (0 : ℝ) τ, criticalSpatialNorm 6 (u r) ≤ C :=
  @MethbokeAddon.WeakFouriermanB.compact_cylinder_spatialNorm_six_bound

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.local_front_compact_cylinder_serrin
example : ∀ (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : LocalPhysicalNSEFront ν T a u p)
    (τ : ℝ) (hτ : 0 < τ) (hτT : τ < T)
    (hcont : ContinuousOn (fun z : ℝ × Vec => u z.1 z.2)
      (Icc (0 : ℝ) τ ×ˢ unitCube)),
    MemLp (fun r => criticalSpatialNorm 6 (u r)) 4
      (volume.restrict (Ioc (0 : ℝ) τ)) :=
  @MethbokeAddon.WeakFouriermanB.local_front_compact_cylinder_serrin

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.compact_cylinder_velocity_bound"
#check @MethbokeAddon.WeakFouriermanB.compact_cylinder_velocity_bound
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.compact_cylinder_velocity_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.compact_cylinder_velocity_bound"
#print axioms MethbokeAddon.WeakFouriermanB.compact_cylinder_velocity_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.compact_cylinder_velocity_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.spatialNorm_six_le_constant_of_cube_bound"
#check @MethbokeAddon.WeakFouriermanB.spatialNorm_six_le_constant_of_cube_bound
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.spatialNorm_six_le_constant_of_cube_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.spatialNorm_six_le_constant_of_cube_bound"
#print axioms MethbokeAddon.WeakFouriermanB.spatialNorm_six_le_constant_of_cube_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.spatialNorm_six_le_constant_of_cube_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.compact_cylinder_spatialNorm_six_bound"
#check @MethbokeAddon.WeakFouriermanB.compact_cylinder_spatialNorm_six_bound
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.compact_cylinder_spatialNorm_six_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.compact_cylinder_spatialNorm_six_bound"
#print axioms MethbokeAddon.WeakFouriermanB.compact_cylinder_spatialNorm_six_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.compact_cylinder_spatialNorm_six_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_compact_cylinder_serrin"
#check @MethbokeAddon.WeakFouriermanB.local_front_compact_cylinder_serrin
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.local_front_compact_cylinder_serrin"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.local_front_compact_cylinder_serrin"
#print axioms MethbokeAddon.WeakFouriermanB.local_front_compact_cylinder_serrin
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.local_front_compact_cylinder_serrin"

