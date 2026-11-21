import QFAHeatGenerator.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.HeatSemigroup
open MethbokeAddon.QuasiFeffermanA.HeatTrajectory
open MethbokeAddon.QuasiFeffermanA.HeatGenerator
open scoped BigOperators NNReal Topology

noncomputable section

example (ν : ℝ≥0) (v : SpatialL2) :
    Continuous (fun t : ℝ => heatL2 ν t.toNNReal v) :=
  heatL2_realTime_continuous ν v

example (ν : ℝ≥0) (v : SpatialL2) :
    heatL2 ν (0 : ℝ).toNNReal v = v :=
  heatL2_realTime_zero ν v

example (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => heatL2 ν s.toNNReal (physicalH1Velocity a))
      ((ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t)) t :=
  heatH1_velocity_hasDerivAt ν hν a ht

example (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    (T : ℝ) (hT : 0 ≤ T) :
    MemLp (fun t : ℝ => physicalH2Laplacian (heatTrajectory ν hν a t))
      2 (volume.restrict (Ioc (0 : ℝ) T)) :=
  heatTrajectory_laplacian_memLp_two ν hν a T hT

example (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    (T : ℝ) (hT : 0 ≤ T) :
    MemLp (fun t : ℝ => (ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t))
      2 (volume.restrict (Ioc (0 : ℝ) T)) :=
  heatH1_velocity_timeDerivative_memLp_two ν hν a T hT

example (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable
      (fun t : ℝ => (ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t))
      volume 0 T :=
  heatH1_velocity_timeDerivative_intervalIntegrable ν hν a T hT

example (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    (T : ℝ) (hT : 0 ≤ T) :
    heatL2 ν T.toNNReal (physicalH1Velocity a) - physicalH1Velocity a =
      ∫ t in (0 : ℝ)..T,
        (ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t) :=
  heatH1_velocity_integrated_equation ν hν a T hT

/- The energy consumer expands physical enstrophy into the actual three
weak gradient norms at the original and terminal H1 traces. -/
example (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T,
        ‖(ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t)‖ ^ 2) =
      (ν : ℝ) / 2 *
        ((∑ j : Fin 3, ‖physicalH1Gradient j a‖ ^ 2) -
          ∑ j : Fin 3, ‖physicalH1Gradient j (heatH1 ν T.toNNReal a)‖ ^ 2) := by
  simpa only [physicalH1Enstrophy] using
    heatH1_velocity_timeDerivative_sq_integral ν hν a T hT

example (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T,
        ‖(ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t)‖ ^ 2) ≤
      (ν : ℝ) / 2 * (∑ j : Fin 3, ‖physicalH1Gradient j a‖ ^ 2) := by
  simpa only [physicalH1Enstrophy] using
    heatH1_velocity_timeDerivative_sq_integral_le ν hν a T hT

/- One actual continuous L2 heat path carries the original initial trace,
the strong derivative, the L2-in-time derivative, and the Bochner equation. -/
example (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1) :
    ∃ v : ℝ → SpatialL2,
      Continuous v ∧ v 0 = physicalH1Velocity a ∧
      (∀ t : ℝ, 0 < t →
        HasDerivAt v ((ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t)) t) ∧
      ∀ T : ℝ, 0 ≤ T →
        MemLp (fun t : ℝ => (ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t))
            2 (volume.restrict (Ioc (0 : ℝ) T)) ∧
          v T - physicalH1Velocity a =
            ∫ t in (0 : ℝ)..T,
              (ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t) := by
  refine ⟨fun t => heatL2 ν t.toNNReal (physicalH1Velocity a),
    heatL2_realTime_continuous ν (physicalH1Velocity a),
    heatL2_realTime_zero ν (physicalH1Velocity a), ?_, ?_⟩
  · intro t ht
    exact heatH1_velocity_hasDerivAt ν hν a ht
  · intro T hT
    exact ⟨heatH1_velocity_timeDerivative_memLp_two ν hν a T hT,
      heatH1_velocity_integrated_equation ν hν a T hT⟩

/- Ordinary positive real viscosity retains exactly the same physical
coefficient in the generator and integrated equation. -/
example (ν : ℝ) (hν : 0 < ν) (a : PhysicalH1)
    (T : ℝ) (hT : 0 ≤ T) :
    heatL2 ν.toNNReal T.toNNReal (physicalH1Velocity a) - physicalH1Velocity a =
      ∫ t in (0 : ℝ)..T,
        ν • physicalH2Laplacian
          (heatTrajectory ν.toNNReal (Real.toNNReal_pos.mpr hν) a t) := by
  simpa only [Real.coe_toNNReal ν hν.le] using
    heatH1_velocity_integrated_equation ν.toNNReal (Real.toNNReal_pos.mpr hν) a T hT


#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatL2_realTime_continuous"
#check @MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatL2_realTime_continuous
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatL2_realTime_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatL2_realTime_continuous"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatL2_realTime_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatL2_realTime_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatL2_realTime_zero"
#check @MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatL2_realTime_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatL2_realTime_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatL2_realTime_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatL2_realTime_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatL2_realTime_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_hasDerivAt"
#check @MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_hasDerivAt"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatTrajectory_laplacian_memLp_two"
#check @MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatTrajectory_laplacian_memLp_two
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatTrajectory_laplacian_memLp_two"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatTrajectory_laplacian_memLp_two"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatTrajectory_laplacian_memLp_two
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatTrajectory_laplacian_memLp_two"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_memLp_two"
#check @MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_memLp_two
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_memLp_two"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_memLp_two"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_memLp_two
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_memLp_two"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_intervalIntegrable"
#check @MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_intervalIntegrable
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_intervalIntegrable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_intervalIntegrable"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_intervalIntegrable
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_intervalIntegrable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_integrated_equation"
#check @MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_integrated_equation
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_integrated_equation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_integrated_equation"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_integrated_equation
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_integrated_equation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_sq_integral"
#check @MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_sq_integral
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_sq_integral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_sq_integral"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_sq_integral
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_sq_integral"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_sq_integral_le"
#check @MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_sq_integral_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_sq_integral_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_sq_integral_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_sq_integral_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatGenerator.heatH1_velocity_timeDerivative_sq_integral_le"
