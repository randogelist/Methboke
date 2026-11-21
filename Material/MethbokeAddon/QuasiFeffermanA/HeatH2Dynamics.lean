import MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup
import MethbokeAddon.QuasiFeffermanA.HeatGenerator

/-!
# Actual H2 heat dynamics in the physical L2 velocity space

For actual H2 initial data, velocity injectivity identifies the accepted
positive-time H1-to-H2 smoothing trajectory with the actual H2 semigroup.
The accepted strong L2 generator and integral equation therefore apply
to this same H2 path. Its initial value is the original H2 datum; the
arbitrary zero extension of the smoothing trajectory is never substituted
for that initial trace. The two paths are compared only at positive times.

The Laplacian path is continuous through zero. Positive-time derivatives
below are derivatives of the SpatialL2 velocity, not H2-valued derivatives.
No derivative, regularity or time-integrability witness is supplied.
This is a free-heat bridge, not a forced equation or maximal-regularity proof.

Prepared source requires matching external compilation and independent
named type/axiom evidence. No local Lean, Lake or kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory
open scoped NNReal Topology

namespace MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics

open HeatH2Semigroup HeatTrajectory

/-- Positive elapsed times identify the smoothing trajectory with the true
H2 heat path. No equality with the smoothing zero extension is claimed. -/
theorem heatTrajectory_eq_heatH2 (ν : ℝ≥0) (hν : 0 < ν)
    (u : PhysicalH2) {t : ℝ} (ht : 0 < t) :
    heatTrajectory ν hν (physicalH2ToH1 u) t = heatH2 ν t.toNNReal u := by
  apply physicalH2Velocity_injective
  rw [heatTrajectory_velocity ν hν (physicalH2ToH1 u) ht,
    physicalH2ToH1_velocity, heatH2_velocity]

/-- The actual Laplacian is continuous down to its original H2 trace.
The real-time clock holds that trace fixed at nonpositive times. -/
theorem heatH2_laplacian_realTime_continuous (ν : ℝ≥0) (u : PhysicalH2) :
    Continuous (fun t : ℝ => physicalH2Laplacian (heatH2 ν t.toNNReal u)) :=
  physicalH2Laplacian.continuous.comp
    ((heatH2_continuous ν u).comp continuous_real_toNNReal)

/-- The actual H2 heat velocity has strong L2 derivative equal to viscosity
times the physical Laplacian of the same path at every positive time. -/
theorem heatH2_velocity_hasDerivAt (ν : ℝ≥0) (hν : 0 < ν)
    (u : PhysicalH2) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun r : ℝ => physicalH2Velocity (heatH2 ν r.toNNReal u))
      ((ν : ℝ) • physicalH2Laplacian (heatH2 ν t.toNNReal u)) t := by
  have hd := HeatGenerator.heatH1_velocity_hasDerivAt ν hν (physicalH2ToH1 u) ht
  rw [heatTrajectory_eq_heatH2 ν hν u ht] at hd
  simpa only [heatH2_velocity, physicalH2ToH1_velocity] using hd

/-- The L2 integral equation starts from the original H2 velocity trace and
holds for every finite nonnegative horizon, including the zero window. -/
theorem heatH2_velocity_integrated_equation (ν : ℝ≥0) (hν : 0 < ν)
    (u : PhysicalH2) (T : ℝ) (hT : 0 ≤ T) :
    physicalH2Velocity (heatH2 ν T.toNNReal u) - physicalH2Velocity u =
      ∫ t in (0 : ℝ)..T,
        (ν : ℝ) • physicalH2Laplacian (heatH2 ν t.toNNReal u) := by
  calc
    _ = ∫ t in (0 : ℝ)..T,
        (ν : ℝ) • physicalH2Laplacian
          (heatTrajectory ν hν (physicalH2ToH1 u) t) := by
      simpa only [heatH2_velocity, physicalH2ToH1_velocity] using
        HeatGenerator.heatH1_velocity_integrated_equation ν hν (physicalH2ToH1 u) T hT
    _ = _ := by
      apply intervalIntegral.integral_congr_Ioo_of_le hT
      intro t ht
      rw [heatTrajectory_eq_heatH2 ν hν u ht.1]

end MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics
