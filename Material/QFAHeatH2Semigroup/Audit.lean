import QFAHeatH2Semigroup.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.HeatSemigroup
open MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup
open scoped BigOperators NNReal Topology

noncomputable section

example (ν t : ℝ≥0) (u : PhysicalH2) : PhysicalH2 := heatH2 ν t u

example (ν t : ℝ≥0) (u : PhysicalH2) :
    physicalH2Velocity (heatH2 ν t u) = heatL2 ν t (physicalH2Velocity u) :=
  heatH2_velocity ν t u

example (ν t : ℝ≥0) (u : PhysicalH2) (j : Fin 3) :
    physicalH2Gradient j (heatH2 ν t u) = heatL2 ν t (physicalH2Gradient j u) :=
  heatH2_gradient ν t u j

example (ν t : ℝ≥0) (u : PhysicalH2) (j k : Fin 3) :
    physicalH2Hessian j k (heatH2 ν t u) = heatL2 ν t (physicalH2Hessian j k u) :=
  heatH2_hessian ν t u j k

example (ν t : ℝ≥0) (u : PhysicalH2) :
    physicalH2Laplacian (heatH2 ν t u) = heatL2 ν t (physicalH2Laplacian u) :=
  heatH2_laplacian ν t u

example (ν t : ℝ≥0) (u : PhysicalH2) :
    physicalH2ToH1 (heatH2 ν t u) = heatH1 ν t (physicalH2ToH1 u) :=
  heatH2_toH1 ν t u

example (ν t : ℝ≥0) (u v : PhysicalH2) :
    heatH2 ν t (u + v) = heatH2 ν t u + heatH2 ν t v :=
  heatH2_add ν t u v

example (ν t : ℝ≥0) (r : ℝ) (u : PhysicalH2) :
    heatH2 ν t (r • u) = r • heatH2 ν t u :=
  heatH2_smul ν t r u

example (ν t : ℝ≥0) (u : PhysicalH2) :
    ‖heatH2 ν t u‖ ≤ ‖u‖ := norm_heatH2_le ν t u

example (ν t : ℝ≥0) : PhysicalH2 →L[ℝ] PhysicalH2 := heatH2CLM ν t

example (ν t : ℝ≥0) (u : PhysicalH2) :
    heatH2CLM ν t u = heatH2 ν t u := heatH2CLM_apply ν t u

example (ν : ℝ≥0) (u : PhysicalH2) : heatH2 ν 0 u = u := heatH2_zero_time ν u

example (t : ℝ≥0) (u : PhysicalH2) : heatH2 0 t u = u := heatH2_zero_viscosity t u

example (ν s t : ℝ≥0) (u : PhysicalH2) :
    heatH2 ν (s + t) u = heatH2 ν s (heatH2 ν t u) := heatH2_add_time ν s t u

example (ν : ℝ≥0) (u : PhysicalH2) :
    Continuous (fun t : ℝ≥0 => heatH2 ν t u) := heatH2_continuous ν u

/- One actual H2 path carries the original trace and every physical
coordinate at every nonnegative time, with the full graph contraction. -/
example (ν : ℝ≥0) (u : PhysicalH2) :
    ∃ U : ℝ≥0 → PhysicalH2,
      Continuous U ∧ U 0 = u ∧
      ∀ t : ℝ≥0,
        physicalH2Velocity (U t) = heatL2 ν t (physicalH2Velocity u) ∧
        (∀ j : Fin 3, physicalH2Gradient j (U t) = heatL2 ν t (physicalH2Gradient j u)) ∧
        (∀ j k : Fin 3, physicalH2Hessian j k (U t) = heatL2 ν t (physicalH2Hessian j k u)) ∧
        physicalH2Laplacian (U t) = heatL2 ν t (physicalH2Laplacian u) ∧
        ‖U t‖ ≤ ‖u‖ := by
  refine ⟨fun t => heatH2 ν t u, heatH2_continuous ν u, heatH2_zero_time ν u, ?_⟩
  intro t
  exact ⟨heatH2_velocity ν t u, heatH2_gradient ν t u, heatH2_hessian ν t u,
    heatH2_laplacian ν t u, norm_heatH2_le ν t u⟩

/- The actual physical Laplacian is continuous all the way to its original
H2-data trace; this is not an H2-trace assertion for arbitrary H1 data. -/
example (ν : ℝ≥0) (u : PhysicalH2) :
    Continuous (fun t : ℝ≥0 => physicalH2Laplacian (heatH2 ν t u)) ∧
      physicalH2Laplacian (heatH2 ν 0 u) = physicalH2Laplacian u := by
  exact ⟨physicalH2Laplacian.continuous.comp (heatH2_continuous ν u),
    congrArg physicalH2Laplacian (heatH2_zero_time ν u)⟩

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_velocity"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_gradient"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_hessian"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_hessian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_hessian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_hessian"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_hessian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_hessian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_laplacian"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_laplacian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_laplacian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_laplacian"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_laplacian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_laplacian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_toH1"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_toH1
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_toH1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_toH1"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_toH1
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_toH1"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_add"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_add
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_add"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_add
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_smul"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_smul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_smul"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.norm_heatH2_le"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.norm_heatH2_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.norm_heatH2_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.norm_heatH2_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.norm_heatH2_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.norm_heatH2_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2CLM"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2CLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2CLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2CLM"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2CLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2CLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2CLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2CLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2CLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2CLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2CLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2CLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_zero_time"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_zero_time
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_zero_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_zero_time"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_zero_time
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_zero_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_zero_viscosity"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_zero_viscosity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_zero_viscosity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_zero_viscosity"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_zero_viscosity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_zero_viscosity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_add_time"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_add_time
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_add_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_add_time"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_add_time
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_add_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_continuous"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_continuous
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_continuous"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup.heatH2_continuous"

