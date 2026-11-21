import QFAHeatH2Dynamics.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.HeatSemigroup
open MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup
open MethbokeAddon.QuasiFeffermanA.HeatTrajectory
open MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics
open scoped BigOperators NNReal Topology

noncomputable section

/- Actual graph equality is asserted only after strictly positive elapsed time. -/
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH2)
    (t : ℝ) (ht : 0 < t) :
    heatTrajectory ν hν (physicalH2ToH1 u) t = heatH2 ν t.toNNReal u :=
  heatTrajectory_eq_heatH2 ν hν u ht

/- Continuity concerns the literal sum of the three physical Hessian entries. -/
example (ν : ℝ≥0) (u : PhysicalH2) :
    Continuous (fun t : ℝ => ∑ j : Fin 3,
      physicalH2Hessian j j (heatH2 ν t.toNNReal u)) := by
  simpa only [physicalH2Laplacian_apply] using
    heatH2_laplacian_realTime_continuous ν u

/- The actual generator density is Bochner integrable; no witness is assumed. -/
example (ν : ℝ≥0) (u : PhysicalH2) (T : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      (ν : ℝ) • physicalH2Laplacian (heatH2 ν t.toNNReal u)) volume 0 T :=
  ((heatH2_laplacian_realTime_continuous ν u).const_smul (ν : ℝ)).intervalIntegrable 0 T

/- This is a derivative in SpatialL2 of the literal physical heat velocity. -/
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH2)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (fun r : ℝ => heatL2 ν r.toNNReal (physicalH2Velocity u))
      ((ν : ℝ) • ∑ j : Fin 3,
        physicalH2Hessian j j (heatH2 ν t.toNNReal u)) t := by
  simpa only [heatH2_velocity, physicalH2Laplacian_apply] using
    heatH2_velocity_hasDerivAt ν hν u ht

/- The original datum and the literal physical Laplacian enter the integral. -/
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH2)
    (T : ℝ) (hT : 0 ≤ T) :
    heatL2 ν T.toNNReal (physicalH2Velocity u) - physicalH2Velocity u =
      ∫ t in (0 : ℝ)..T, (ν : ℝ) • ∑ j : Fin 3,
        physicalH2Hessian j j (heatH2 ν t.toNNReal u) := by
  simpa only [heatH2_velocity, physicalH2Laplacian_apply] using
    heatH2_velocity_integrated_equation ν hν u T hT

/- One constructed path retains its original H2 trace, all positive-time L2
   derivatives and all nonnegative-window integral equations simultaneously. -/
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH2) :
    ∃ w : ℝ → PhysicalH2,
      Continuous w ∧ w 0 = u ∧
      (∀ t : ℝ, w t = heatH2 ν t.toNNReal u) ∧
      (∀ t : ℝ, 0 < t →
        HasDerivAt (fun r : ℝ => physicalH2Velocity (w r))
          ((ν : ℝ) • physicalH2Laplacian (w t)) t) ∧
      (∀ T : ℝ, 0 ≤ T →
        physicalH2Velocity (w T) - physicalH2Velocity u =
          ∫ t in (0 : ℝ)..T, (ν : ℝ) • physicalH2Laplacian (w t)) := by
  refine ⟨fun t : ℝ => heatH2 ν t.toNNReal u,
    (heatH2_continuous ν u).comp continuous_real_toNNReal, ?_, ?_, ?_, ?_⟩
  · simpa only [Real.toNNReal_zero] using heatH2_zero_time ν u
  · intro t
    rfl
  · intro t ht
    exact heatH2_velocity_hasDerivAt ν hν u ht
  · intro T hT
    exact heatH2_velocity_integrated_equation ν hν u T hT

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatTrajectory_eq_heatH2"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatTrajectory_eq_heatH2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatTrajectory_eq_heatH2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatTrajectory_eq_heatH2"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatTrajectory_eq_heatH2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatTrajectory_eq_heatH2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_laplacian_realTime_continuous"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_laplacian_realTime_continuous
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_laplacian_realTime_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_laplacian_realTime_continuous"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_laplacian_realTime_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_laplacian_realTime_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_velocity_hasDerivAt"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_velocity_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_velocity_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_velocity_hasDerivAt"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_velocity_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_velocity_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_velocity_integrated_equation"
#check @MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_velocity_integrated_equation
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_velocity_integrated_equation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_velocity_integrated_equation"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_velocity_integrated_equation
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics.heatH2_velocity_integrated_equation"

