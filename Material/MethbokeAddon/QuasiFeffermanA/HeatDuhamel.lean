import MethbokeAddon.QuasiFeffermanA.HeatSemigroup
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The actual finite-window L2 Duhamel response

The retarded Bochner integral uses the native real L2 heat semigroup and
the actual forcing values. Joint strong continuity follows from heat
contraction and strong continuity, including at zero elapsed time. It
supplies the integrand's measurability; finite-window MemLp2 supplies its
integrability. No kernel measurability or construction witness is assumed.

The response is linear on admissible forcing, invariant under a.e.
equality on the forcing window, continuous in time with zero initial
trace, and bounded by sqrt(time) times the actual time-L2 forcing norm.
Continuity uses a fixed-window indicator kernel and dominated convergence;
the moving diagonal is a null singleton. No operator-norm continuity at
zero and no spatial derivative of arbitrary L2 forcing is required.

This construction supplies the low-frequency L2 response. Forced H1/H2
maximal regularity and the inhomogeneous differential equation are separate
endpoints. Prepared source requires matching authorized external compiler
and independent exact type/axiom evidence. No local Lean is executed.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace MethbokeAddon.QuasiFeffermanA.HeatDuhamel

open HeatSemigroup

private theorem heatL2_sub (ν t : ℝ≥0) (u v : SpatialL2) :
    heatL2 ν t (u - v) = heatL2 ν t u - heatL2 ν t v :=
  (heatL2CLM ν t).map_sub u v

/-- Joint strong continuity is proved from contraction. It includes zero
elapsed time without an operator-norm continuity assumption. -/
theorem heatL2_joint_continuous (ν : ℝ≥0) :
    Continuous (fun p : ℝ≥0 × SpatialL2 => heatL2 ν p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound (q : ℝ≥0 × SpatialL2) :
      ‖heatL2 ν q.1 q.2 - heatL2 ν p.1 p.2‖ ≤
        ‖q.2 - p.2‖ + ‖heatL2 ν q.1 p.2 - heatL2 ν p.1 p.2‖ := by
    have heq : heatL2 ν q.1 q.2 - heatL2 ν p.1 p.2 =
        heatL2 ν q.1 (q.2 - p.2) +
          (heatL2 ν q.1 p.2 - heatL2 ν p.1 p.2) := by
      rw [heatL2_sub]
      abel
    rw [heq]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_heatL2_le ν q.1 (q.2 - p.2)) le_rfl)
  have hc : Continuous (fun q : ℝ≥0 × SpatialL2 =>
      ‖q.2 - p.2‖ + ‖heatL2 ν q.1 p.2 - heatL2 ν p.1 p.2‖) :=
    (continuous_snd.sub continuous_const).norm.add
      (((heatL2_continuous ν p.2).comp continuous_fst).sub continuous_const).norm
  have hz : Tendsto (fun q : ℝ≥0 × SpatialL2 =>
      ‖q.2 - p.2‖ + ‖heatL2 ν q.1 p.2 - heatL2 ν p.1 p.2‖)
      (𝓝 p) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero, zero_add] using hc.tendsto p
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hz

/-- The native retarded integral. Claims about an admissible forcing
window concern nonnegative times in that window. -/
def duhamelL2 (ν : ℝ≥0) (f : ℝ → SpatialL2) (t : ℝ) : SpatialL2 :=
  ∫ s in (0 : ℝ)..t, heatL2 ν (t - s).toNNReal (f s)

/-- Actual integrand measurability follows from joint strong continuity
and the forcing's ordinary a.e. strong measurability. -/
theorem duhamelL2_integrand_aestronglyMeasurable
    (ν : ℝ≥0) (f : ℝ → SpatialL2) (μ : Measure ℝ)
    (hf : AEStronglyMeasurable f μ) (t : ℝ) :
    AEStronglyMeasurable (fun s : ℝ => heatL2 ν (t - s).toNNReal (f s)) μ := by
  have hclock : Continuous (fun s : ℝ => (t - s).toNNReal) :=
    continuous_real_toNNReal.comp (continuous_const.sub continuous_id)
  exact (heatL2_joint_continuous ν).comp_aestronglyMeasurable
    (hclock.aestronglyMeasurable.prodMk hf)

private theorem forcing_memLp_subwindow
    (f : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    {t : ℝ} (htT : t ≤ T) :
    MemLp f 2 (volume.restrict (Ioc (0 : ℝ) t)) :=
  hf.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc le_rfl htT) le_rfl)

/-- Each actual retarded integrand is itself in L2 on the smaller window. -/
theorem duhamelL2_integrand_memLp_two
    (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : ℝ) (htT : t ≤ T) :
    MemLp (fun s : ℝ => heatL2 ν (t - s).toNNReal (f s))
      2 (volume.restrict (Ioc (0 : ℝ) t)) := by
  have hft := forcing_memLp_subwindow f T hf htT
  exact hft.of_le
    (duhamelL2_integrand_aestronglyMeasurable ν f _ hft.aestronglyMeasurable t)
    (Eventually.of_forall (fun s => norm_heatL2_le ν (t - s).toNNReal (f s)))

/-- Actual Bochner integrability, including the zero-length window. -/
theorem duhamelL2_integrand_intervalIntegrable
    (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    IntervalIntegrable (fun s : ℝ => heatL2 ν (t - s).toNNReal (f s)) volume 0 t :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr
    (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (duhamelL2_integrand_memLp_two ν f T hf t htT))

/-- The actual response has exactly zero initial L2 trace. -/
theorem duhamelL2_zero_time (ν : ℝ≥0) (f : ℝ → SpatialL2) :
    duhamelL2 ν f 0 = 0 := by
  simp only [duhamelL2, intervalIntegral.integral_same]

theorem duhamelL2_zero_forcing (ν : ℝ≥0) (t : ℝ) :
    duhamelL2 ν (fun _ : ℝ => (0 : SpatialL2)) t = 0 := by
  simp only [duhamelL2, heatL2_zero, intervalIntegral.integral_zero]

/-- The response depends only on the forcing's L2 equivalence class on
the original window, not on arbitrary choices of time representatives. -/
theorem duhamelL2_ae_eq
    (ν : ℝ≥0) (f g : ℝ → SpatialL2) (T : ℝ)
    (hfg : f =ᵐ[volume.restrict (Ioc (0 : ℝ) T)] g)
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    duhamelL2 ν f t = duhamelL2 ν g t := by
  rw [duhamelL2, duhamelL2, intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_of_le ht]
  apply integral_congr_ae
  have hfg' : f =ᵐ[volume.restrict (Ioc (0 : ℝ) t)] g :=
    ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl htT) hfg
  filter_upwards [hfg'] with s hs
  rw [hs]

/-- Additivity holds for the constructed Bochner response on every
subwindow of the two actual L2 forcing inputs. -/
theorem duhamelL2_add
    (ν : ℝ≥0) (f g : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    duhamelL2 ν (fun s => f s + g s) t = duhamelL2 ν f t + duhamelL2 ν g t := by
  simp only [duhamelL2, heatL2_add]
  exact intervalIntegral.integral_add
    (duhamelL2_integrand_intervalIntegrable ν f T hf t ht htT)
    (duhamelL2_integrand_intervalIntegrable ν g T hg t ht htT)

theorem duhamelL2_smul (ν : ℝ≥0) (c : ℝ) (f : ℝ → SpatialL2) (t : ℝ) :
    duhamelL2 ν (fun s => c • f s) t = c • duhamelL2 ν f t := by
  simp only [duhamelL2, heatL2_smul, intervalIntegral.integral_smul]

/-- The low-frequency L2 bound follows directly from heat contraction. -/
theorem duhamelL2_norm_le_integral_norm
    (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖duhamelL2 ν f t‖ ≤ ∫ s in (0 : ℝ)..t, ‖f s‖ := by
  have hft := forcing_memLp_subwindow f T hf htT
  have hi : IntervalIntegrable f volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr
      (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hft)
  exact intervalIntegral.norm_integral_le_of_norm_le ht
    (Eventually.of_forall (fun s _ => norm_heatL2_le ν (t - s).toNNReal (f s))) hi.norm

private theorem integral_norm_le_sqrt_mul
    (f : ℝ → SpatialL2) (t : ℝ) (ht : 0 ≤ t)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) t))) :
    (∫ s in (0 : ℝ)..t, ‖f s‖) ≤
      Real.sqrt t * Real.sqrt (∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2) := by
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Ioc (0 : ℝ) t)) :=
    memLp_const 1
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Ioc (0 : ℝ) t))
    Real.HolderConjugate.two_two
    (f := fun _ : ℝ => (1 : ℝ)) (g := fun s : ℝ => ‖f s‖)
    (Eventually.of_forall (fun _ => zero_le_one))
    (Eventually.of_forall (fun s => norm_nonneg (f s)))
    (by simpa only [ENNReal.ofReal_ofNat] using h1)
    (by simpa only [ENNReal.ofReal_ofNat] using hf.norm)
  simpa only [one_mul, Real.one_rpow, Real.rpow_two, ← Real.sqrt_eq_rpow,
    ← intervalIntegral.integral_of_le ht, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul, mul_one] using hcs

/-- Exact square-root-of-time estimate with the actual forcing energy on
the same time interval, with no viscosity or spectral-gap loss. -/
theorem duhamelL2_norm_le_sqrt_mul
    (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖duhamelL2 ν f t‖ ≤
      Real.sqrt t * Real.sqrt (∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2) :=
  (duhamelL2_norm_le_integral_norm ν f T hf t ht htT).trans
    (integral_norm_le_sqrt_mul f t ht (forcing_memLp_subwindow f T hf htT))

/-- One uniform finite-horizon bound controls every time in the window. -/
theorem duhamelL2_norm_le_sqrt_horizon
    (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖duhamelL2 ν f t‖ ≤
      Real.sqrt T * Real.sqrt (∫ s in (0 : ℝ)..T, ‖f s‖ ^ 2) := by
  have hT : 0 ≤ T := ht.trans htT
  have hi : IntervalIntegrable (fun s : ℝ => ‖f s‖ ^ 2) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hf.norm.integrable_sq
  have he : (∫ s in (0 : ℝ)..t, ‖f s‖ ^ 2) ≤
      ∫ s in (0 : ℝ)..T, ‖f s‖ ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl ht htT
      (Eventually.of_forall (fun s => sq_nonneg ‖f s‖)) hi
  exact (duhamelL2_norm_le_sqrt_mul ν f T hf t ht htT).trans
    (mul_le_mul (Real.sqrt_le_sqrt htT) (Real.sqrt_le_sqrt he)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

private theorem forcing_norm_toLp_eq_sqrt
    (f : ℝ → SpatialL2) (T : ℝ) (hT : 0 ≤ T)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T))) :
    ‖hf.toLp f‖ = Real.sqrt (∫ s in (0 : ℝ)..T, ‖f s‖ ^ 2) := by
  have hs : ‖hf.toLp f‖ ^ 2 = ∫ s in (0 : ℝ)..T, ‖f s‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, intervalIntegral.integral_of_le hT]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with s hs
    simp only [hs, real_inner_self_eq_norm_sq]
  simpa only [Real.sqrt_sq_eq_abs, abs_norm] using congrArg Real.sqrt hs

/-- The uniform estimate is stated against the norm of the actual
Bochner L2 forcing class, rather than an independently supplied bound. -/
theorem duhamelL2_norm_le_sqrt_mul_lpNorm
    (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖duhamelL2 ν f t‖ ≤ Real.sqrt T * ‖hf.toLp f‖ := by
  rw [forcing_norm_toLp_eq_sqrt f T (ht.trans htT) hf]
  exact duhamelL2_norm_le_sqrt_horizon ν f T hf t ht htT

private def retardedKernel (ν : ℝ≥0) (f : ℝ → SpatialL2) (t s : ℝ) : SpatialL2 :=
  (Iic t).indicator (fun r : ℝ => heatL2 ν (t - r).toNNReal (f r)) s

private theorem retardedKernel_aestronglyMeasurable
    (ν : ℝ≥0) (f : ℝ → SpatialL2) (μ : Measure ℝ)
    (hf : AEStronglyMeasurable f μ) (t : ℝ) :
    AEStronglyMeasurable (retardedKernel ν f t) μ :=
  (duhamelL2_integrand_aestronglyMeasurable ν f μ hf t).indicator measurableSet_Iic

private theorem retardedKernel_norm_le
    (ν : ℝ≥0) (f : ℝ → SpatialL2) (t s : ℝ) :
    ‖retardedKernel ν f t s‖ ≤ ‖f s‖ := by
  by_cases hst : s ≤ t
  · simpa only [retardedKernel, indicator_of_mem hst] using
      norm_heatL2_le ν (t - s).toNNReal (f s)
  · simpa only [retardedKernel, indicator_of_notMem hst, norm_zero] using norm_nonneg (f s)

private theorem retardedKernel_continuousAt
    (ν : ℝ≥0) (f : ℝ → SpatialL2) (t s : ℝ) (hst : s ≠ t) :
    ContinuousAt (fun r : ℝ => retardedKernel ν f r s) t := by
  rcases lt_or_gt_of_ne hst with hs | hs
  · have hc : Continuous (fun r : ℝ => heatL2 ν (r - s).toNNReal (f s)) :=
      (heatL2_continuous ν (f s)).comp
        (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
    apply hc.continuousAt.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hs] with r hr
    simp only [retardedKernel, indicator_of_mem hr.le]
  · apply (continuousAt_const (y := (0 : SpatialL2))).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hs] with r hr
    simp only [retardedKernel, indicator_of_notMem (not_le_of_gt hr)]

private theorem fixedWindow_response_continuous
    (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T))) :
    Continuous (fun t : ℝ => ∫ s in Ioc (0 : ℝ) T, retardedKernel ν f t s) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun s : ℝ => ‖f s‖)
  · exact Eventually.of_forall (fun r =>
      retardedKernel_aestronglyMeasurable ν f _ hf.aestronglyMeasurable r)
  · exact Eventually.of_forall (fun r =>
      Eventually.of_forall (fun s => retardedKernel_norm_le ν f r s))
  · exact (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf).norm
  · filter_upwards [(volume.restrict (Ioc (0 : ℝ) T)).ae_ne t] with s hs
    exact (retardedKernel_continuousAt ν f t s hs).tendsto

private theorem duhamelL2_eq_fixedWindow
    (ν : ℝ≥0) (f : ℝ → SpatialL2) (T t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    duhamelL2 ν f t = ∫ s in Ioc (0 : ℝ) T, retardedKernel ν f t s := by
  rw [duhamelL2, ← intervalIntegral.integral_indicator ht,
    intervalIntegral.integral_of_le (ht.1.trans ht.2)]
  rfl

/-- The constructed response is continuous on the whole finite time
window, including its exact zero initial trace. -/
theorem duhamelL2_continuousOn
    (ν : ℝ≥0) (f : ℝ → SpatialL2) (T : ℝ) (hT : 0 ≤ T)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T))) :
    ContinuousOn (duhamelL2 ν f) (Icc (0 : ℝ) T) := by
  apply (fixedWindow_response_continuous ν f T hf).continuousOn.congr
  intro t ht
  exact duhamelL2_eq_fixedWindow ν f T t ht

end MethbokeAddon.QuasiFeffermanA.HeatDuhamel
