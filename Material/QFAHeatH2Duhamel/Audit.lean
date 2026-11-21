import QFAHeatH2Duhamel.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.HeatSemigroup
open MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup
open MethbokeAddon.QuasiFeffermanA.HeatDuhamel
open MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel
open scoped NNReal Topology

noncomputable section

example (ν : ℝ≥0) :
    Continuous (fun p : ℝ≥0 × PhysicalH2 => heatH2 ν p.1 p.2) :=
  heatH2_joint_continuous ν

/- The response is the literal Bochner integral in the actual H2 graph. -/
example (ν : ℝ≥0) (f : ℝ → PhysicalH2) (t : ℝ) :
    duhamelH2 ν f t =
      ∫ s in (0 : ℝ)..t, heatH2 ν (t - s).toNNReal (f s) := rfl

example (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) :
    Continuous (fun p : ℝ × ℝ => heatH2 ν (p.1 - p.2).toNNReal (f p.2)) :=
  duhamelH2_integrand_continuous ν f hf

example (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => heatH2 ν (t - s).toNNReal (f s)) volume 0 t :=
  duhamelH2_integrand_intervalIntegrable ν f hf t

example (ν : ℝ≥0) (f : ℝ → PhysicalH2) :
    duhamelH2 ν f 0 = (0 : PhysicalH2) :=
  duhamelH2_zero_time ν f

/- Continuity concerns the actual H2-valued integral, including time zero. -/
example (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) :
    Continuous (fun t : ℝ =>
      ∫ s in (0 : ℝ)..t, heatH2 ν (t - s).toNNReal (f s)) :=
  duhamelH2_continuous ν f hf

/- The original coordinate forcing is retained inside the literal L2 response. -/
example (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) (t : ℝ) :
    physicalH2Velocity (duhamelH2 ν f t) =
      ∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (physicalH2Velocity (f s)) :=
  duhamelH2_velocity ν f hf t

example (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) (t : ℝ) (j : Fin 3) :
    physicalH2Gradient j (duhamelH2 ν f t) =
      ∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (physicalH2Gradient j (f s)) :=
  duhamelH2_gradient ν f hf t j

example (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f)
    (t : ℝ) (j k : Fin 3) :
    physicalH2Hessian j k (duhamelH2 ν f t) =
      ∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (physicalH2Hessian j k (f s)) :=
  duhamelH2_hessian ν f hf t j k

example (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) (t : ℝ) :
    physicalH2Laplacian (duhamelH2 ν f t) =
      ∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (physicalH2Laplacian (f s)) :=
  duhamelH2_laplacian ν f hf t

example (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) (t : ℝ) :
    physicalH2ToH1 (duhamelH2 ν f t) =
      ∫ s in (0 : ℝ)..t, heatH1 ν (t - s).toNNReal (physicalH2ToH1 (f s)) :=
  duhamelH2_toH1 ν f hf t

example (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) (t : ℝ) (ht : 0 ≤ t) :
    ‖duhamelH2 ν f t‖ ≤ ∫ s in (0 : ℝ)..t, ‖f s‖ :=
  duhamelH2_norm_le_integral_norm ν f hf t ht

/- One actual H2 response carries continuity, zero trace, the literal
integral, both original velocity/Laplacian forcings and the full H2 bound. -/
example (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) :
    ∃ U : ℝ → PhysicalH2,
      Continuous U ∧ U 0 = 0 ∧
      ∀ t : ℝ,
        U t = (∫ s in (0 : ℝ)..t, heatH2 ν (t - s).toNNReal (f s)) ∧
        physicalH2Velocity (U t) =
          (∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (physicalH2Velocity (f s))) ∧
        physicalH2Laplacian (U t) =
          (∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (physicalH2Laplacian (f s))) ∧
        (0 ≤ t → ‖U t‖ ≤ ∫ s in (0 : ℝ)..t, ‖f s‖) := by
  refine ⟨duhamelH2 ν f, duhamelH2_continuous ν f hf,
    duhamelH2_zero_time ν f, ?_⟩
  intro t
  exact ⟨rfl, duhamelH2_velocity ν f hf t, duhamelH2_laplacian ν f hf t,
    fun ht => duhamelH2_norm_le_integral_norm ν f hf t ht⟩

/- Zero viscosity gives the actual H2 primitive, with no positivity premise. -/
example (f : ℝ → PhysicalH2) (t : ℝ) :
    duhamelH2 0 f t = ∫ s in (0 : ℝ)..t, f s := by
  simp only [duhamelH2, heatH2_zero_viscosity]

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.heatH2_joint_continuous"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.heatH2_joint_continuous
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.heatH2_joint_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.heatH2_joint_continuous"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.heatH2_joint_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.heatH2_joint_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_integrand_continuous"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_integrand_continuous
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_integrand_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_integrand_continuous"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_integrand_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_integrand_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_integrand_intervalIntegrable"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_integrand_intervalIntegrable
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_integrand_intervalIntegrable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_integrand_intervalIntegrable"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_integrand_intervalIntegrable
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_integrand_intervalIntegrable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_zero_time"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_zero_time
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_zero_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_zero_time"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_zero_time
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_zero_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_continuous"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_continuous
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_continuous"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_velocity"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_gradient"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_hessian"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_hessian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_hessian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_hessian"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_hessian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_hessian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_laplacian"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_laplacian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_laplacian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_laplacian"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_laplacian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_laplacian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_toH1"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_toH1
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_toH1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_toH1"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_toH1
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_toH1"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_norm_le_integral_norm"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_norm_le_integral_norm
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_norm_le_integral_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_norm_le_integral_norm"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_norm_le_integral_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel.duhamelH2_norm_le_integral_norm"

