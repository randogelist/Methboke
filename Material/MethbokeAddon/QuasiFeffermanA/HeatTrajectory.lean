import MethbokeAddon.QuasiFeffermanA.HeatSmoothing
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# The actual positive-time H2 heat trajectory

The previously constructed positive-time H1-to-H2 operator is assembled into
a real-time trajectory. The value at nonpositive times is set to zero only
to supply a total measurable function: no H2 initial trace is asserted.
At every positive time its velocity and H1 inclusion are exactly the
physical heat semigroup. A fixed positive smoothing step and the H1
semigroup law prove H2 continuity locally at every positive time.

Continuity away from the single time zero gives strong measurability on the
whole real time line. The exact physical H2 norm decomposition supplies the
pointwise input for the separate time-integrated heat-energy construction.
No time-integrability or trajectory-regularity witness is an input.

Matching cached external compiler, independent type consumers and named
standard-only axiom reports are required. No local Lean is executed.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory Filter
open scoped NNReal Topology

namespace MethbokeAddon.QuasiFeffermanA.HeatTrajectory

open HeatSemigroup HeatSmoothing

/-- The actual positive-time H2 heat trajectory, with an arbitrary zero
extension at nonpositive times. Its H1 initial trace is handled separately. -/
def heatTrajectory (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (t : ℝ) : PhysicalH2 :=
  if ht : 0 < t then
    heatH1ToH2 ν t.toNNReal hν (Real.toNNReal_pos.mpr ht) u
  else 0

theorem heatTrajectory_eq_of_pos (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1)
    {t : ℝ} (ht : 0 < t) :
    heatTrajectory ν hν u t =
      heatH1ToH2 ν t.toNNReal hν (Real.toNNReal_pos.mpr ht) u := by
  simp only [heatTrajectory, dif_pos ht]

theorem heatTrajectory_eq_zero_of_nonpos (ν : ℝ≥0) (hν : 0 < ν)
    (u : PhysicalH1) {t : ℝ} (ht : t ≤ 0) : heatTrajectory ν hν u t = 0 := by
  simp only [heatTrajectory, dif_neg (not_lt.mpr ht)]

theorem heatTrajectory_velocity (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1)
    {t : ℝ} (ht : 0 < t) :
    physicalH2Velocity (heatTrajectory ν hν u t) =
      heatL2 ν t.toNNReal (physicalH1Velocity u) := by
  rw [heatTrajectory_eq_of_pos ν hν u ht, heatH1ToH2_velocity]

theorem heatTrajectory_toH1 (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1)
    {t : ℝ} (ht : 0 < t) :
    physicalH2ToH1 (heatTrajectory ν hν u t) = heatH1 ν t.toNNReal u := by
  rw [heatTrajectory_eq_of_pos ν hν u ht, heatH1ToH2_toH1]

/-- The same positive-time trajectory factors through any earlier fixed
positive smoothing time; equality is in the actual physical H2 graph. -/
theorem heatTrajectory_factor (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1)
    (s : ℝ≥0) (hs : 0 < s) {t : ℝ} (hst : (s : ℝ) < t) :
    heatTrajectory ν hν u t =
      heatH1ToH2CLM ν s hν hs (heatH1 ν (t - (s : ℝ)).toNNReal u) := by
  have hs' : 0 < (s : ℝ) := hs
  have ht : 0 < t := lt_trans hs' hst
  have htime : t.toNNReal = s + (t - (s : ℝ)).toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, Real.coe_toNNReal t ht.le,
      Real.coe_toNNReal (t - (s : ℝ)) (sub_nonneg.mpr hst.le)]
    ring
  apply physicalH2Velocity_injective
  rw [heatTrajectory_velocity ν hν u ht, heatH1ToH2CLM_apply,
    heatH1ToH2_velocity, heatH1_velocity, htime, heatL2_add_time]

/-- H2 continuity follows from a fixed positive smoothing step composed with
the accepted strongly continuous H1 heat semigroup. -/
theorem heatTrajectory_continuousAt_pos (ν : ℝ≥0) (hν : 0 < ν)
    (u : PhysicalH1) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (heatTrajectory ν hν u) t := by
  let s : ℝ≥0 := (t / 2).toNNReal
  have hs : 0 < s := Real.toNNReal_pos.mpr (half_pos ht)
  have hst : (s : ℝ) < t := by
    dsimp only [s]
    rw [Real.coe_toNNReal (t / 2) (half_pos ht).le]
    linarith
  have hclock : Continuous (fun r : ℝ => (r - (s : ℝ)).toNNReal) :=
    continuous_real_toNNReal.comp (continuous_id.sub continuous_const)
  have hc : Continuous (fun r : ℝ =>
      heatH1ToH2CLM ν s hν hs (heatH1 ν (r - (s : ℝ)).toNNReal u)) :=
    (heatH1ToH2CLM ν s hν hs).continuous.comp
      ((heatH1_continuous ν u).comp hclock)
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hst] with r hr
  exact heatTrajectory_factor ν hν u s hs hr

theorem heatTrajectory_continuousAt_neg (ν : ℝ≥0) (hν : 0 < ν)
    (u : PhysicalH1) {t : ℝ} (ht : t < 0) :
    ContinuousAt (heatTrajectory ν hν u) t := by
  apply (continuousAt_const (c := (0 : PhysicalH2))).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds ht] with r hr
  exact heatTrajectory_eq_zero_of_nonpos ν hν u hr.le

theorem heatTrajectory_continuousOn_pos (ν : ℝ≥0) (hν : 0 < ν)
    (u : PhysicalH1) : ContinuousOn (heatTrajectory ν hν u) (Set.Ioi 0) := by
  intro t ht
  exact (heatTrajectory_continuousAt_pos ν hν u ht).continuousWithinAt

theorem heatTrajectory_continuousOn_ne_zero (ν : ℝ≥0) (hν : 0 < ν)
    (u : PhysicalH1) :
    ContinuousOn (heatTrajectory ν hν u) ({0}ᶜ : Set ℝ) := by
  intro t ht
  have hne : t ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
  rcases lt_or_gt_of_ne hne with hn | hp
  · exact (heatTrajectory_continuousAt_neg ν hν u hn).continuousWithinAt
  · exact (heatTrajectory_continuousAt_pos ν hν u hp).continuousWithinAt

/-- Real time is second-countable, so the constructed H2 path is strongly
measurable even though no H2 value at the initial trace is required. -/
theorem heatTrajectory_stronglyMeasurable (ν : ℝ≥0) (hν : 0 < ν)
    (u : PhysicalH1) : StronglyMeasurable (heatTrajectory ν hν u) := by
  apply (heatTrajectory_continuousOn_ne_zero ν hν u).stronglyMeasurable_of_countable_compl
  simpa only [compl_compl] using (Set.countable_singleton (0 : ℝ))

theorem heatTrajectory_laplacian_stronglyMeasurable (ν : ℝ≥0) (hν : 0 < ν)
    (u : PhysicalH1) :
    StronglyMeasurable (fun t : ℝ => physicalH2Laplacian (heatTrajectory ν hν u t)) :=
  physicalH2Laplacian.continuous.comp_stronglyMeasurable
    (heatTrajectory_stronglyMeasurable ν hν u)

theorem heatTrajectory_laplacian_sq_stronglyMeasurable (ν : ℝ≥0) (hν : 0 < ν)
    (u : PhysicalH1) :
    StronglyMeasurable (fun t : ℝ => ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2) :=
  (heatTrajectory_laplacian_stronglyMeasurable ν hν u).norm.pow 2

/-- The inhomogeneous H2 norm uses the exact physical heat H1 trace and
actual Laplacian. This is an identity, with no integrability premise. -/
theorem heatTrajectory_norm_sq (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1)
    {t : ℝ} (ht : 0 < t) :
    ‖heatTrajectory ν hν u t‖ ^ 2 =
      ‖heatH1 ν t.toNNReal u‖ ^ 2 +
        ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2 := by
  rw [heatTrajectory_eq_of_pos ν hν u ht,
    H2Spectral.physicalH2_norm_sq_eq_laplacian, physicalH1_norm_sq]
  simp only [heatH1ToH2_velocity, heatH1ToH2_gradient, heatH1_velocity,
    heatH1_gradient, physicalH1Energy, physicalH1Enstrophy]

/-- Uniform H1 contraction leaves only the actual Laplacian energy to be
integrated in order to prove finite-window L2-time H2 membership. -/
theorem heatTrajectory_norm_sq_le (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1)
    (t : ℝ) :
    ‖heatTrajectory ν hν u t‖ ^ 2 ≤
      ‖u‖ ^ 2 + ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2 := by
  by_cases ht : 0 < t
  · rw [heatTrajectory_norm_sq ν hν u ht]
    exact add_le_add_right (heatH1_norm_sq_le ν t.toNNReal u) _
  · rw [heatTrajectory_eq_zero_of_nonpos ν hν u (le_of_not_gt ht)]
    simpa only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      map_zero, add_zero] using (sq_nonneg ‖u‖)

end MethbokeAddon.QuasiFeffermanA.HeatTrajectory
