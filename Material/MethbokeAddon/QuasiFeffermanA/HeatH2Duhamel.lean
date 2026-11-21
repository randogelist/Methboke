import MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup
import MethbokeAddon.QuasiFeffermanA.HeatDuhamel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual H2 Duhamel response for continuous physical H2 forcing

The retarded Bochner integral is constructed in the complete actual
PhysicalH2 graph. Joint strong continuity of the H2 heat action gives a
jointly continuous kernel for every ordinary continuous H2 forcing.
Native parametric interval integration then proves continuity of the
response, including its exact zero initial trace. All thirteen physical
coordinates, the Laplacian and the H2-to-H1 map commute with the actual
integral. The velocity and Laplacian agree with the existing physical
L2 Duhamel constructor for the corresponding original forcing fields.

The real-time definition uses the nonnegative elapsed-time clock; physical
retarded evolution concerns t >= 0. Continuity of this defined extension
holds on the whole real line. No forcing regularity beyond Continuous f
and no response, integrability or continuity witness is assumed.

This is the regular-forcing construction. It asserts no inhomogeneous
derivative equation or maximal regularity for arbitrary L2 forcing.
Prepared source requires matching external compilation and independent
named type/axiom evidence. No local Lean, Lake or kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal Topology

namespace MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel

open HeatSemigroup HeatH2Semigroup HeatDuhamel

private theorem heatH2_sub (ν t : ℝ≥0) (u v : PhysicalH2) :
    heatH2 ν t (u - v) = heatH2 ν t u - heatH2 ν t v :=
  (heatH2CLM ν t).map_sub u v

/-- Joint strong continuity of the actual H2 action, including zero elapsed time. -/
theorem heatH2_joint_continuous (ν : ℝ≥0) :
    Continuous (fun p : ℝ≥0 × PhysicalH2 => heatH2 ν p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound (q : ℝ≥0 × PhysicalH2) :
      ‖heatH2 ν q.1 q.2 - heatH2 ν p.1 p.2‖ ≤
        ‖q.2 - p.2‖ + ‖heatH2 ν q.1 p.2 - heatH2 ν p.1 p.2‖ := by
    have heq : heatH2 ν q.1 q.2 - heatH2 ν p.1 p.2 =
        heatH2 ν q.1 (q.2 - p.2) +
          (heatH2 ν q.1 p.2 - heatH2 ν p.1 p.2) := by
      rw [heatH2_sub]
      abel
    rw [heq]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_heatH2_le ν q.1 (q.2 - p.2)) le_rfl)
  have hc : Continuous (fun q : ℝ≥0 × PhysicalH2 =>
      ‖q.2 - p.2‖ + ‖heatH2 ν q.1 p.2 - heatH2 ν p.1 p.2‖) :=
    (continuous_snd.sub continuous_const).norm.add
      (((heatH2_continuous ν p.2).comp continuous_fst).sub continuous_const).norm
  have hz : Tendsto (fun q : ℝ≥0 × PhysicalH2 =>
      ‖q.2 - p.2‖ + ‖heatH2 ν q.1 p.2 - heatH2 ν p.1 p.2‖)
      (𝓝 p) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero, zero_add] using hc.tendsto p
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hz

/-- Actual retarded integration takes place in the complete physical H2 graph. -/
def duhamelH2 (ν : ℝ≥0) (f : ℝ → PhysicalH2) (t : ℝ) : PhysicalH2 :=
  ∫ s in (0 : ℝ)..t, heatH2 ν (t - s).toNNReal (f s)

/-- Ordinary continuous H2 forcing gives a jointly continuous physical kernel. -/
theorem duhamelH2_integrand_continuous
    (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) :
    Continuous (fun p : ℝ × ℝ => heatH2 ν (p.1 - p.2).toNNReal (f p.2)) := by
  have hclock : Continuous (fun p : ℝ × ℝ => (p.1 - p.2).toNNReal) :=
    continuous_real_toNNReal.comp (continuous_fst.sub continuous_snd)
  have hpair : Continuous (fun p : ℝ × ℝ => ((p.1 - p.2).toNNReal, f p.2)) :=
    hclock.prodMk (hf.comp continuous_snd)
  exact (heatH2_joint_continuous ν).comp hpair

/-- The constructed H2 kernel is genuinely Bochner integrable on every finite window. -/
theorem duhamelH2_integrand_intervalIntegrable
    (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => heatH2 ν (t - s).toNNReal (f s)) volume 0 t := by
  have hpair : Continuous (fun s : ℝ => (t, s)) :=
    continuous_const.prodMk continuous_id
  exact ((duhamelH2_integrand_continuous ν f hf).comp hpair).intervalIntegrable 0 t

/-- The original zero trace is an exact equality in PhysicalH2. -/
theorem duhamelH2_zero_time (ν : ℝ≥0) (f : ℝ → PhysicalH2) :
    duhamelH2 ν f 0 = 0 := by
  simp only [duhamelH2, intervalIntegral.integral_same]

/-- The actual regular-forcing response is H2-continuous through time zero. -/
theorem duhamelH2_continuous
    (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) :
    Continuous (duhamelH2 ν f) := by
  change Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t,
    heatH2 ν (t - s).toNNReal (f s))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := 0)
    (f := fun t s : ℝ => heatH2 ν (t - s).toNNReal (f s))
    (duhamelH2_integrand_continuous ν f hf) continuous_id

/-- The actual velocity is the existing physical L2 response to the original velocity forcing. -/
theorem duhamelH2_velocity
    (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) (t : ℝ) :
    physicalH2Velocity (duhamelH2 ν f t) =
      duhamelL2 ν (fun s => physicalH2Velocity (f s)) t := by
  simpa only [duhamelH2, duhamelL2, heatH2_velocity] using
    (physicalH2Velocity.intervalIntegral_comp_comm
      (duhamelH2_integrand_intervalIntegrable ν f hf t)).symm

/-- Each actual first derivative is the L2 response to its original gradient forcing. -/
theorem duhamelH2_gradient
    (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) (t : ℝ) (j : Fin 3) :
    physicalH2Gradient j (duhamelH2 ν f t) =
      duhamelL2 ν (fun s => physicalH2Gradient j (f s)) t := by
  simpa only [duhamelH2, duhamelL2, heatH2_gradient] using
    ((physicalH2Gradient j).intervalIntegral_comp_comm
      (duhamelH2_integrand_intervalIntegrable ν f hf t)).symm

/-- Each actual Hessian entry is the L2 response to its original Hessian forcing. -/
theorem duhamelH2_hessian
    (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) (t : ℝ) (j k : Fin 3) :
    physicalH2Hessian j k (duhamelH2 ν f t) =
      duhamelL2 ν (fun s => physicalH2Hessian j k (f s)) t := by
  simpa only [duhamelH2, duhamelL2, heatH2_hessian] using
    ((physicalH2Hessian j k).intervalIntegral_comp_comm
      (duhamelH2_integrand_intervalIntegrable ν f hf t)).symm

/-- The actual Laplacian is the L2 response to the original physical Laplacian forcing. -/
theorem duhamelH2_laplacian
    (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) (t : ℝ) :
    physicalH2Laplacian (duhamelH2 ν f t) =
      duhamelL2 ν (fun s => physicalH2Laplacian (f s)) t := by
  simpa only [duhamelH2, duhamelL2, heatH2_laplacian] using
    (physicalH2Laplacian.intervalIntegral_comp_comm
      (duhamelH2_integrand_intervalIntegrable ν f hf t)).symm

/-- The actual H1 inclusion gives the literal retarded integral of the existing H1 heat action. -/
theorem duhamelH2_toH1
    (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) (t : ℝ) :
    physicalH2ToH1 (duhamelH2 ν f t) =
      ∫ s in (0 : ℝ)..t, heatH1 ν (t - s).toNNReal (physicalH2ToH1 (f s)) := by
  simpa only [duhamelH2, heatH2_toH1] using
    (physicalH2ToH1.intervalIntegral_comp_comm
      (duhamelH2_integrand_intervalIntegrable ν f hf t)).symm

/-- The full physical H2 response obeys the actual forcing integral bound. -/
theorem duhamelH2_norm_le_integral_norm
    (ν : ℝ≥0) (f : ℝ → PhysicalH2) (hf : Continuous f) (t : ℝ) (ht : 0 ≤ t) :
    ‖duhamelH2 ν f t‖ ≤ ∫ s in (0 : ℝ)..t, ‖f s‖ := by
  change ‖∫ s in (0 : ℝ)..t, heatH2 ν (t - s).toNNReal (f s)‖ ≤
    ∫ s in (0 : ℝ)..t, ‖f s‖
  exact intervalIntegral.norm_integral_le_of_norm_le ht
    (Eventually.of_forall (fun s _ => norm_heatH2_le ν (t - s).toNNReal (f s)))
    (hf.norm.intervalIntegrable 0 t)

end MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel
