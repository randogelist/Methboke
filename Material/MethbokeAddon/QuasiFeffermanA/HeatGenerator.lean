import MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# The actual L2 heat generator and its Bochner integral equation

For arbitrary physical H1 data, the true heat velocity has strong L2 time
derivative `nu * Delta` at every positive time. Scalar difference quotients
are bounded uniformly on a neighborhood separated from zero. Plancherel
and dominated convergence against the datum's actual L2 Fourier energy
then prove convergence of the L2 difference quotients. No derivative or
regularity witness is supplied as an input.

The actual H2 trajectory and its finite-time dissipation give MemLp2 and
Bochner integrability of that derivative down to time zero. FTC uses only
positive-time derivatives and the true heat velocity's continuous initial
trace. Its integral equation includes T=0.
The arbitrary zero extension of the H2 trajectory is used only for the
derivative and time integrals, never as the initial velocity.

This is a free linear heat construction. Forced heat, maximal regularity
for forcing, and nonlinear H1 local existence remain separate endpoints.
Matching authorized external compiler and independent literal type/axiom
evidence are required. No local Lean, Lake, kernel or cache execution is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators FourierTransform NNReal ENNReal Topology

namespace MethbokeAddon.QuasiFeffermanA.HeatGenerator

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open HeatSemigroup HeatSmoothing HeatTrajectory HeatTimeEnergy

private def heatScalar (ν : ℝ≥0) (t : ℝ) (ξ : Space) : ℝ :=
  Real.exp (-((ν : ℝ) * heatRate ξ * t))

private theorem heatValue_eq_heatScalar (ν t : ℝ≥0) (ξ : Space) :
    heatValue ν t ξ = heatScalar ν (t : ℝ) ξ := by
  unfold heatValue heatScalar heatRate
  congr 1
  ring

private theorem heatScalar_hasDerivAt (ν : ℝ≥0) (ξ : Space) (t : ℝ) :
    HasDerivAt (fun r : ℝ => heatScalar ν r ξ)
      (-((ν : ℝ) * heatRate ξ) * heatScalar ν t ξ) t := by
  have hd : HasDerivAt (fun r : ℝ => heatScalar ν r ξ)
      (heatScalar ν t ξ * (-((ν : ℝ) * heatRate ξ))) t := by
    simpa only [heatScalar, neg_mul] using
      (hasDerivAt_const_mul (x := t) (-((ν : ℝ) * heatRate ξ))).exp
  exact hd.congr_deriv (mul_comm _ _)

/- A uniform scalar bound is used only on a neighborhood separated from
zero. It is never integrated as a singular estimate at the initial time. -/
private theorem heatScalar_derivative_norm_le (ν : ℝ≥0)
    (α t : ℝ) (hα : 0 < α) (hαt : α ≤ t) (ξ : Space) :
    ‖-((ν : ℝ) * heatRate ξ) * heatScalar ν t ξ‖ ≤ α⁻¹ := by
  let c : ℝ := (ν : ℝ) * heatRate ξ
  have hc : 0 ≤ c := mul_nonneg ν.property (heatRate_nonneg ξ)
  have hq : heatScalar ν t ξ ≤ heatScalar ν α ξ := by
    apply Real.exp_le_exp.mpr
    change -(c * t) ≤ -(c * α)
    exact neg_le_neg (mul_le_mul_of_nonneg_left hαt hc)
  have hb : α * (c * heatScalar ν α ξ) ≤ 1 := by
    calc
      α * (c * heatScalar ν α ξ) =
          (c * α) * Real.exp (-(c * α)) := by
        dsimp only [heatScalar, c]
        ring
      _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one _
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hb' : c * heatScalar ν α ξ ≤ α⁻¹ := by
    apply (mul_le_mul_iff_of_pos_left hα).mp
    simpa only [mul_inv_cancel₀ (ne_of_gt hα)] using hb
  change ‖-c * heatScalar ν t ξ‖ ≤ α⁻¹
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hc,
    abs_of_pos (show 0 < heatScalar ν t ξ from Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left hq hc).trans hb'

private theorem heatScalar_slope_norm_le (ν : ℝ≥0)
    (α t r : ℝ) (hα : 0 < α) (hαt : α ≤ t) (hαr : α ≤ r)
    (ξ : Space) :
    ‖slope (fun s : ℝ => heatScalar ν s ξ) t r‖ ≤ α⁻¹ := by
  by_cases hrt : r = t
  · subst r
    simpa only [slope_same, norm_zero] using (inv_nonneg.mpr hα.le)
  have hm : ‖heatScalar ν r ξ - heatScalar ν t ξ‖ ≤ α⁻¹ * ‖r - t‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s (_hs : s ∈ Ici α) =>
        (heatScalar_hasDerivAt ν ξ s).hasDerivWithinAt)
      (fun s (hs : s ∈ Ici α) =>
        heatScalar_derivative_norm_le ν α s hα hs ξ)
      (convex_Ici α) hαt hαr
  rw [slope_def_field, norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hrt))).mpr hm

private def scalarSlopeError (ν : ℝ≥0) (t r : ℝ) (ξ : Space) : ℝ :=
  slope (fun s : ℝ => heatScalar ν s ξ) t r -
    (-((ν : ℝ) * heatRate ξ) * heatScalar ν t ξ)

private theorem scalarSlopeError_continuous_frequency
    (ν : ℝ≥0) (t r : ℝ) : Continuous (scalarSlopeError ν t r) := by
  unfold scalarSlopeError
  simp only [slope_def_field]
  unfold heatScalar heatRate
  fun_prop

private theorem scalarSlopeError_norm_le (ν : ℝ≥0)
    (α t r : ℝ) (hα : 0 < α) (hαt : α ≤ t) (hαr : α ≤ r)
    (ξ : Space) : ‖scalarSlopeError ν t r ξ‖ ≤ 2 * α⁻¹ := by
  have hs := heatScalar_slope_norm_le ν α t r hα hαt hαr ξ
  have hd := heatScalar_derivative_norm_le ν α t hα hαt ξ
  unfold scalarSlopeError
  exact (norm_sub_le _ _).trans (by linarith)

private theorem scalarSlopeError_tendsto (ν : ℝ≥0) (t : ℝ) (ξ : Space) :
    Tendsto (fun r : ℝ => scalarSlopeError ν t r ξ)
      (𝓝[≠] t) (𝓝 (0 : ℝ)) := by
  simpa only [scalarSlopeError, sub_self] using
    (heatScalar_hasDerivAt ν ξ t).tendsto_slope.sub
      (tendsto_const_nhds (x := -((ν : ℝ) * heatRate ξ) * heatScalar ν t ξ))

private theorem fourier_complexify_sub (u v : SpatialL2) :
    (𝓕 (complexifyL2 (u - v)) : ComplexL2) =
      (𝓕 (complexifyL2 u) : ComplexL2) - (𝓕 (complexifyL2 v) : ComplexL2) := by
  change (Lp.fourierTransformₗᵢ Space ComplexVector) (complexifyL2LI (u - v)) =
    (Lp.fourierTransformₗᵢ Space ComplexVector) (complexifyL2LI u) -
      (Lp.fourierTransformₗᵢ Space ComplexVector) (complexifyL2LI v)
  rw [map_sub, map_sub]

private theorem fourier_complexify_smul (r : ℝ) (u : SpatialL2) :
    (𝓕 (complexifyL2 (r • u)) : ComplexL2) =
      (r : ℂ) • (𝓕 (complexifyL2 u) : ComplexL2) := by
  rw [complexifyL2_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  change (Lp.fourierTransformₗᵢ Space ComplexVector) ((r : ℂ) • complexifyL2 u) =
    (r : ℂ) • (Lp.fourierTransformₗᵢ Space ComplexVector) (complexifyL2 u)
  exact map_smul _ _ _

private theorem heat_slope_error_fourier_ae
    (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    (fun ξ : Space =>
      (𝓕 (complexifyL2
        (slope (fun s : ℝ => heatL2 ν s.toNNReal (physicalH1Velocity a)) t r -
          (ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t))) : ComplexL2) ξ)
      =ᵐ[volume] (fun ξ : Space =>
        (scalarSlopeError ν t r ξ : ℂ) •
          (𝓕 (complexifyL2 (physicalH1Velocity a)) : ComplexL2) ξ) := by
  let s : ℝ := (r - t)⁻¹
  let Ar : ComplexL2 := 𝓕 (complexifyL2 (heatL2 ν r.toNNReal (physicalH1Velocity a)))
  let At : ComplexL2 := 𝓕 (complexifyL2 (heatL2 ν t.toNNReal (physicalH1Velocity a)))
  let L : ComplexL2 := 𝓕 (complexifyL2 (physicalH2Laplacian (heatTrajectory ν hν a t)))
  have hΔ : (fun ξ : Space => L ξ) =ᵐ[volume]
      (fun ξ : Space =>
        ((-heatRate ξ * heatValue ν t.toNNReal ξ : ℝ) : ℂ) •
          (𝓕 (complexifyL2 (physicalH1Velocity a)) : ComplexL2) ξ) := by
    dsimp only [L]
    rw [heatTrajectory_eq_of_pos ν hν a ht]
    exact heatH1ToH2_laplacian_fourier_ae ν t.toNNReal hν
      (Real.toNNReal_pos.mpr ht) a
  simp only [slope_def_module, fourier_complexify_sub, fourier_complexify_smul]
  change (fun ξ : Space =>
      (((s : ℂ) • (Ar - At) - ((ν : ℝ) : ℂ) • L) : ComplexL2) ξ)
    =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub ((s : ℂ) • (Ar - At)) (((ν : ℝ) : ℂ) • L),
    Lp.coeFn_smul (s : ℂ) (Ar - At), Lp.coeFn_sub Ar At,
    Lp.coeFn_smul ((ν : ℝ) : ℂ) L,
    heatL2_fourier_ae ν r.toNNReal (physicalH1Velocity a),
    heatL2_fourier_ae ν t.toNNReal (physicalH1Velocity a), hΔ]
      with ξ hsub hsmul hdiff hsmulL hrF htF hL
  rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hdiff, Pi.sub_apply,
    hsmulL, Pi.smul_apply, hrF, htF, hL,
    ← sub_smul, smul_smul, smul_smul, ← sub_smul]
  have hc : s * (heatValue ν r.toNNReal ξ - heatValue ν t.toNNReal ξ) -
      (ν : ℝ) * (-heatRate ξ * heatValue ν t.toNNReal ξ) =
        scalarSlopeError ν t r ξ := by
    simp only [heatValue_eq_heatScalar, Real.coe_toNNReal r hr.le,
      Real.coe_toNNReal t ht.le, scalarSlopeError, slope_def_field, s,
      div_eq_mul_inv]
    ring
  congr 1
  simpa only [Complex.ofReal_sub, Complex.ofReal_mul] using congrArg Complex.ofReal hc

private theorem heat_slope_error_norm_sq_eq_fourier
    (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ‖slope (fun s : ℝ => heatL2 ν s.toNNReal (physicalH1Velocity a)) t r -
      (ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t)‖ ^ 2 =
      ∫ ξ : Space, (scalarSlopeError ν t r ξ) ^ 2 *
        ‖(𝓕 (complexifyL2 (physicalH1Velocity a)) : ComplexL2) ξ‖ ^ 2 := by
  calc
    _ = ∫ ξ : Space,
        ‖(𝓕 (complexifyL2
          (slope (fun s : ℝ => heatL2 ν s.toNNReal (physicalH1Velocity a)) t r -
            (ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t))) : ComplexL2) ξ‖ ^ 2 :=
      (H1Spectral.integral_fourier_energy _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [heat_slope_error_fourier_ae ν hν a ht hr] with ξ hξ
      rw [hξ, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem integral_scalarSlopeError_sq_tendsto
    (ν : ℝ≥0) (a : PhysicalH1) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun r : ℝ => ∫ ξ : Space, (scalarSlopeError ν t r ξ) ^ 2 *
      ‖(𝓕 (complexifyL2 (physicalH1Velocity a)) : ComplexL2) ξ‖ ^ 2)
      (𝓝[≠] t) (𝓝 (0 : ℝ)) := by
  let α : ℝ := t / 2
  have hα : 0 < α := half_pos ht
  have hαt : α ≤ t := (half_lt_self ht).le
  have hαlt : α < t := half_lt_self ht
  have hnear : ∀ᶠ r : ℝ in 𝓝[≠] t, α < r :=
    (eventually_gt_nhds hαlt).filter_mono nhdsWithin_le_nhds
  have hdct : Tendsto
      (fun r : ℝ => ∫ ξ : Space, (scalarSlopeError ν t r ξ) ^ 2 *
        ‖(𝓕 (complexifyL2 (physicalH1Velocity a)) : ComplexL2) ξ‖ ^ 2)
      (𝓝[≠] t) (𝓝 (∫ _ξ : Space, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := fun ξ : Space => (2 * α⁻¹) ^ 2 *
        ‖(𝓕 (complexifyL2 (physicalH1Velocity a)) : ComplexL2) ξ‖ ^ 2)
    · filter_upwards with r
      exact ((scalarSlopeError_continuous_frequency ν t r).aestronglyMeasurable.pow 2).mul
        ((Lp.aestronglyMeasurable
          (𝓕 (complexifyL2 (physicalH1Velocity a)) : ComplexL2)).norm.pow 2)
    · filter_upwards [hnear] with r hr
      filter_upwards with ξ
      have hb : (scalarSlopeError ν t r ξ) ^ 2 ≤ (2 * α⁻¹) ^ 2 := by
        have hs := pow_le_pow_left₀ (norm_nonneg (scalarSlopeError ν t r ξ))
          (scalarSlopeError_norm_le ν α t r hα hαt hr.le ξ) 2
        simpa only [Real.norm_eq_abs, sq_abs] using hs
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    · exact (H1Spectral.integrable_fourier_energy (physicalH1Velocity a)).const_mul
        ((2 * α⁻¹) ^ 2)
    · filter_upwards with ξ
      have hs := ((scalarSlopeError_tendsto ν t ξ).pow 2).mul
        (tendsto_const_nhds (x :=
          ‖(𝓕 (complexifyL2 (physicalH1Velocity a)) : ComplexL2) ξ‖ ^ 2))
      simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul] using hs
  simpa only [integral_zero] using hdct

/-- The true real-time heat velocity is strongly continuous, including its
actual initial trace. Negative times are held at that trace by `toNNReal`. -/
theorem heatL2_realTime_continuous (ν : ℝ≥0) (v : SpatialL2) :
    Continuous (fun t : ℝ => heatL2 ν t.toNNReal v) :=
  (heatL2_continuous ν v).comp continuous_real_toNNReal

/-- The true heat path retains the supplied initial L2 datum exactly. -/
theorem heatL2_realTime_zero (ν : ℝ≥0) (v : SpatialL2) :
    heatL2 ν (0 : ℝ).toNNReal v = v := by
  rw [Real.toNNReal_zero, heatL2_zero_time]

/-- Strong L2 time differentiation of the actual physical H1 heat path.
The derivative is the physical graph Laplacian of the same H2 trajectory. -/
theorem heatH1_velocity_hasDerivAt
    (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun r : ℝ => heatL2 ν r.toNNReal (physicalH1Velocity a))
      ((ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t)) t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hnear : ∀ᶠ r : ℝ in 𝓝[≠] t, 0 < r :=
    (eventually_gt_nhds ht).filter_mono nhdsWithin_le_nhds
  have hsq : Tendsto
      (fun r : ℝ =>
        ‖slope (fun s : ℝ => heatL2 ν s.toNNReal (physicalH1Velocity a)) t r -
          (ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t)‖ ^ 2)
      (𝓝[≠] t) (𝓝 (0 : ℝ)) := by
    apply (integral_scalarSlopeError_sq_tendsto ν a ht).congr'
    filter_upwards [hnear] with r hr
    exact (heat_slope_error_norm_sq_eq_fourier ν hν a ht hr).symm
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

/-- The actual Laplacian, not a supplied realization, belongs to L2 in time. -/
theorem heatTrajectory_laplacian_memLp_two
    (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    (T : ℝ) (hT : 0 ≤ T) :
    MemLp (fun t : ℝ => physicalH2Laplacian (heatTrajectory ν hν a t))
      2 (volume.restrict (Ioc (0 : ℝ) T)) :=
  physicalH2Laplacian.comp_memLp' (heatTrajectory_memLp_two ν hν a T hT)

/-- Finite-time L2 membership of the exact strong L2 time derivative. -/
theorem heatH1_velocity_timeDerivative_memLp_two
    (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    (T : ℝ) (hT : 0 ≤ T) :
    MemLp (fun t : ℝ =>
      (ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t))
      2 (volume.restrict (Ioc (0 : ℝ) T)) :=
  (heatTrajectory_laplacian_memLp_two ν hν a T hT).const_smul (ν : ℝ)

/-- Actual Bochner integrability down to time zero comes from the finite
L2-time norm; no singular positive-time estimate is integrated at zero. -/
theorem heatH1_velocity_timeDerivative_intervalIntegrable
    (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (fun t : ℝ =>
      (ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t)) volume 0 T :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
    (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (heatH1_velocity_timeDerivative_memLp_two ν hν a T hT))

/-- The free heat equation as an equality of actual L2 classes and a
Bochner time integral, with the original physical initial trace. -/
theorem heatH1_velocity_integrated_equation
    (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    (T : ℝ) (hT : 0 ≤ T) :
    heatL2 ν T.toNNReal (physicalH1Velocity a) - physicalH1Velocity a =
      ∫ t in (0 : ℝ)..T,
        (ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t) := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (heatL2_realTime_continuous ν (physicalH1Velocity a)).continuousOn
    (fun t (ht : t ∈ Ioo (0 : ℝ) T) => heatH1_velocity_hasDerivAt ν hν a ht.1)
    (heatH1_velocity_timeDerivative_intervalIntegrable ν hν a T hT)
  simpa only [heatL2_realTime_zero] using hftc.symm

/-- Exact time-derivative energy retains both the viscosity and the actual
terminal H1 trace. The initial datum is only required to be physical H1. -/
theorem heatH1_velocity_timeDerivative_sq_integral
    (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T,
      ‖(ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t)‖ ^ 2) =
      (ν : ℝ) / 2 *
        (physicalH1Enstrophy a - physicalH1Enstrophy (heatH1 ν T.toNNReal a)) := by
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [intervalIntegral.integral_const_mul,
    heatTrajectory_laplacian_sq_integral ν hν a T hT]
  have hν0 : (ν : ℝ) ≠ 0 := ne_of_gt hν
  field_simp [hν0] <;> ring

/-- Quantitative finite-window derivative control for arbitrary physical
H1 initial data, with no extra regularity or time-integrability premise. -/
theorem heatH1_velocity_timeDerivative_sq_integral_le
    (ν : ℝ≥0) (hν : 0 < ν) (a : PhysicalH1)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T,
      ‖(ν : ℝ) • physicalH2Laplacian (heatTrajectory ν hν a t)‖ ^ 2) ≤
      (ν : ℝ) / 2 * physicalH1Enstrophy a := by
  rw [heatH1_velocity_timeDerivative_sq_integral ν hν a T hT]
  exact mul_le_mul_of_nonneg_left
    (sub_le_self _ (physicalH1Enstrophy_nonneg _))
    (div_nonneg ν.property (by norm_num))

end MethbokeAddon.QuasiFeffermanA.HeatGenerator
