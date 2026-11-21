import MethbokeAddon.QuasiFeffermanA.HeatTrajectory
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Exact finite-time free-heat enstrophy dissipation

For arbitrary actual physical H1 data, the nonnegative density
`lambda * exp (-(2*nu*lambda)*t) * (lambda * norm (Fourier u)^2)`
has an explicitly integrated scalar primitive. Its time integral is bounded
by the original integrable enstrophy density divided by `2*nu`. Tonelli's
integrability criterion therefore proves joint integrability before Fubini
is used. No time-integrability premise and no integration of the singular
pointwise `1/t` estimate is involved.

The accepted physical Laplacian Fourier formula identifies the spatial
integral with the squared L2 norm of the actual constructed H2 trajectory.
The exact enstrophy-dissipation identity, finite-window H2 square
integrability and a quantitative H2 time bound follow. The H2 trajectory is
zero at nonpositive times; its value at the single initial time makes no
claim that arbitrary H1 data belong to H2.

These are free linear heat estimates. No heat generator, Duhamel operator,
nonlinear local solution or nonzero-data QFA conclusion is asserted here.
Prepared source requires matching external compiler and independent exact
type/axiom evidence. No local Lean, Lake or kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators FourierTransform NNReal Topology

namespace MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open HeatSemigroup HeatSmoothing HeatTrajectory

/-- The actual integrable Fourier density of physical H1 enstrophy. -/
def enstrophyDensity (u : PhysicalH1) (ξ : Space) : ℝ :=
  heatRate ξ * ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2

theorem enstrophyDensity_nonneg (u : PhysicalH1) (ξ : Space) :
    0 ≤ enstrophyDensity u ξ :=
  mul_nonneg (heatRate_nonneg ξ) (sq_nonneg _)

theorem integrable_enstrophyDensity (u : PhysicalH1) :
    Integrable (enstrophyDensity u) volume := by
  change Integrable (fun ξ : Space => (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
    ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) volume
  exact H1Spectral.integrable_fourier_gradient (physicalH1_weakGradient u)

theorem integral_enstrophyDensity (u : PhysicalH1) :
    (∫ ξ : Space, enstrophyDensity u ξ) = physicalH1Enstrophy u := by
  simpa only [enstrophyDensity, heatRate, physicalH1Enstrophy] using
    H1Spectral.integral_fourier_gradient (physicalH1_weakGradient u)

private theorem heatValue_sq_eq_exp (ν t : ℝ≥0) (ξ : Space) :
    heatValue ν t ξ ^ 2 =
      Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * (t : ℝ)) := by
  unfold heatValue
  rw [pow_two, ← Real.exp_add]
  congr 1
  unfold heatRate
  ring

private theorem enstrophyDensity_heatH1_ae (ν t : ℝ≥0) (u : PhysicalH1) :
    enstrophyDensity (heatH1 ν t u) =ᵐ[volume]
      (fun ξ : Space =>
        Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * (t : ℝ)) *
          enstrophyDensity u ξ) := by
  filter_upwards [heatL2_fourier_ae ν t (physicalH1Velocity u)] with ξ hξ
  dsimp only [enstrophyDensity]
  rw [heatH1_velocity, hξ, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, heatValue_sq_eq_exp]
  ring

private theorem integrable_heatEnstrophyDensity (ν t : ℝ≥0) (u : PhysicalH1) :
    Integrable (fun ξ : Space =>
      Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * (t : ℝ)) *
        enstrophyDensity u ξ) volume :=
  (integrable_enstrophyDensity (heatH1 ν t u)).congr
    (enstrophyDensity_heatH1_ae ν t u)

/-- Enstrophy of the actual H1 heat action, with the original input density. -/
theorem heatH1_enstrophy_eq_integral (ν t : ℝ≥0) (u : PhysicalH1) :
    physicalH1Enstrophy (heatH1 ν t u) =
      ∫ ξ : Space, Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * (t : ℝ)) *
        enstrophyDensity u ξ := by
  rw [← integral_enstrophyDensity (heatH1 ν t u)]
  exact integral_congr_ae (enstrophyDensity_heatH1_ae ν t u)

/-- Nonnegative real-time density of the squared physical heat Laplacian. -/
def heatDissipationDensity (ν : ℝ≥0) (u : PhysicalH1) (t : ℝ) (ξ : Space) : ℝ :=
  heatRate ξ * Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * t) *
    enstrophyDensity u ξ

theorem heatDissipationDensity_nonneg (ν : ℝ≥0) (u : PhysicalH1)
    (t : ℝ) (ξ : Space) : 0 ≤ heatDissipationDensity ν u t ξ :=
  mul_nonneg (mul_nonneg (heatRate_nonneg ξ) (Real.exp_pos _).le)
    (enstrophyDensity_nonneg u ξ)

private theorem heatDissipationDensity_continuous_time (ν : ℝ≥0)
    (u : PhysicalH1) (ξ : Space) :
    Continuous (fun t : ℝ => heatDissipationDensity ν u t ξ) := by
  unfold heatDissipationDensity
  fun_prop

private theorem heatDissipationDensity_aestronglyMeasurable (ν : ℝ≥0)
    (u : PhysicalH1) (μ : Measure ℝ) :
    AEStronglyMeasurable
      (fun q : Space × ℝ => heatDissipationDensity ν u q.2 q.1)
      ((volume : Measure Space).prod μ) := by
  have hc : Continuous (fun q : Space × ℝ =>
      heatRate q.1 * Real.exp (-(2 * (ν : ℝ) * heatRate q.1) * q.2)) := by
    unfold heatRate
    fun_prop
  exact hc.aestronglyMeasurable.mul
    (integrable_enstrophyDensity u).aestronglyMeasurable.comp_fst

private theorem heatDissipationDensity_primitive_hasDerivAt
    (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (ξ : Space) (t : ℝ) :
    HasDerivAt
      (fun r : ℝ => -enstrophyDensity u ξ / (2 * (ν : ℝ)) *
        Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * r))
      (heatDissipationDensity ν u t ξ) t := by
  have hc : 2 * (ν : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt hν)
  have hd := ((hasDerivAt_const_mul (x := t)
    (-(2 * (ν : ℝ) * heatRate ξ))).exp).const_mul
      (-enstrophyDensity u ξ / (2 * (ν : ℝ)))
  convert hd using 1 <;> try rfl
  unfold heatDissipationDensity
  field_simp [hc] <;> ring

/-- Exact scalar time integration includes zero frequency without dividing
by its frequency. The only positive denominator is the given viscosity. -/
theorem integral_heatDissipationDensity_time
    (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T)
    (ξ : Space) :
    (∫ t in Ioc (0 : ℝ) T, heatDissipationDensity ν u t ξ) =
      (2 * (ν : ℝ))⁻¹ * (enstrophyDensity u ξ -
        Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * T) * enstrophyDensity u ξ) := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => heatDissipationDensity_primitive_hasDerivAt ν hν u ξ t)
    ((heatDissipationDensity_continuous_time ν u ξ).intervalIntegrable 0 T)
  rw [intervalIntegral.integral_of_le hT] at hftc
  calc
    (∫ t in Ioc (0 : ℝ) T, heatDissipationDensity ν u t ξ) =
        -enstrophyDensity u ξ / (2 * (ν : ℝ)) *
          Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * T) -
        (-enstrophyDensity u ξ / (2 * (ν : ℝ)) *
          Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * 0)) := hftc
    _ = _ := by simp only [mul_zero, Real.exp_zero, mul_one, div_eq_mul_inv]; ring

/-- Tonelli's native integrability criterion is discharged by the exact
time integral and the input's genuine integrable enstrophy density. -/
theorem integrable_heatDissipationDensity_prod
    (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    Integrable (fun q : Space × ℝ => heatDissipationDensity ν u q.2 q.1)
      ((volume : Measure Space).prod (volume.restrict (Ioc (0 : ℝ) T))) := by
  have hsm := heatDissipationDensity_aestronglyMeasurable ν u
    (volume.restrict (Ioc (0 : ℝ) T))
  apply (integrable_prod_iff hsm).mpr
  constructor
  · filter_upwards with ξ
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
      ((heatDissipationDensity_continuous_time ν u ξ).intervalIntegrable 0 T)
  · apply ((integrable_enstrophyDensity u).const_mul ((2 * (ν : ℝ))⁻¹)).mono'
      hsm.norm.integral_prod_right'
    filter_upwards with ξ
    have hn : (∫ t in Ioc (0 : ℝ) T, ‖heatDissipationDensity ν u t ξ‖) =
        ∫ t in Ioc (0 : ℝ) T, heatDissipationDensity ν u t ξ := by
      apply integral_congr_ae
      filter_upwards with t
      exact Real.norm_of_nonneg (heatDissipationDensity_nonneg ν u t ξ)
    rw [hn, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg (fun t => heatDissipationDensity_nonneg ν u t ξ)),
      integral_heatDissipationDensity_time ν hν u T hT ξ]
    exact mul_le_mul_of_nonneg_left
      (sub_le_self _ (mul_nonneg (Real.exp_pos _).le (enstrophyDensity_nonneg u ξ)))
      (inv_nonneg.mpr (mul_nonneg (by norm_num) ν.property))

/-- The literal physical Laplacian matches the nonnegative density. -/
theorem heatH1ToH2_laplacian_norm_sq_eq_integral
    (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) :
    ‖physicalH2Laplacian (heatH1ToH2 ν t hν ht u)‖ ^ 2 =
      ∫ ξ : Space, heatDissipationDensity ν u (t : ℝ) ξ := by
  calc
    ‖physicalH2Laplacian (heatH1ToH2 ν t hν ht u)‖ ^ 2 =
        ∫ ξ : Space,
          ‖(𝓕 (complexifyL2
            (physicalH2Laplacian (heatH1ToH2 ν t hν ht u))) : ComplexL2) ξ‖ ^ 2 :=
      (H1Spectral.integral_fourier_energy _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [heatH1ToH2_laplacian_fourier_ae ν t hν ht u] with ξ hξ
      rw [hξ]
      simp only [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
        sq_abs, neg_sq]
      rw [heatValue_sq_eq_exp]
      unfold heatDissipationDensity enstrophyDensity
      ring

private theorem integral_heatDissipationDensity_space_time
    (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Ioc (0 : ℝ) T, ∫ ξ : Space, heatDissipationDensity ν u t ξ) =
      (2 * (ν : ℝ))⁻¹ *
        (physicalH1Enstrophy u - physicalH1Enstrophy (heatH1 ν T.toNNReal u)) := by
  have hprod := integrable_heatDissipationDensity_prod ν hν u T hT
  have hdamped : Integrable (fun ξ : Space =>
      Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * T) * enstrophyDensity u ξ) volume := by
    simpa only [Real.coe_toNNReal T hT] using
      integrable_heatEnstrophyDensity ν T.toNNReal u
  have htrace : (∫ ξ : Space,
      Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * T) * enstrophyDensity u ξ) =
      physicalH1Enstrophy (heatH1 ν T.toNNReal u) := by
    simpa only [Real.coe_toNNReal T hT] using
      (heatH1_enstrophy_eq_integral ν T.toNNReal u).symm
  calc
    (∫ t in Ioc (0 : ℝ) T, ∫ ξ : Space, heatDissipationDensity ν u t ξ) =
        ∫ ξ : Space, ∫ t in Ioc (0 : ℝ) T, heatDissipationDensity ν u t ξ :=
      (integral_integral_swap hprod).symm
    _ = ∫ ξ : Space, (2 * (ν : ℝ))⁻¹ * (enstrophyDensity u ξ -
        Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * T) * enstrophyDensity u ξ) := by
      apply integral_congr_ae
      filter_upwards with ξ
      exact integral_heatDissipationDensity_time ν hν u T hT ξ
    _ = (2 * (ν : ℝ))⁻¹ * ((∫ ξ : Space, enstrophyDensity u ξ) -
        ∫ ξ : Space, Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * T) *
          enstrophyDensity u ξ) := by
      rw [integral_const_mul, integral_sub (integrable_enstrophyDensity u) hdamped]
    _ = _ := by rw [integral_enstrophyDensity, htrace]

/-- Actual trajectory Laplacian at every positive real time. -/
theorem heatTrajectory_laplacian_norm_sq_eq_integral
    (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) {t : ℝ} (ht : 0 < t) :
    ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2 =
      ∫ ξ : Space, heatDissipationDensity ν u t ξ := by
  rw [heatTrajectory_eq_of_pos ν hν u ht]
  simpa only [Real.coe_toNNReal t ht.le] using
    heatH1ToH2_laplacian_norm_sq_eq_integral ν t.toNNReal hν
      (Real.toNNReal_pos.mpr ht) u

/-- Squared actual Laplacian is integrable all the way down to time zero. -/
theorem heatTrajectory_laplacian_sq_integrableOn
    (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    IntegrableOn (fun t : ℝ => ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2)
      (Ioc (0 : ℝ) T) volume := by
  apply (integrable_heatDissipationDensity_prod ν hν u T hT).integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (heatTrajectory_laplacian_norm_sq_eq_integral ν hν u ht.1).symm

theorem heatTrajectory_laplacian_sq_intervalIntegrable
    (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable
      (fun t : ℝ => ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2)
      volume 0 T :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
    (heatTrajectory_laplacian_sq_integrableOn ν hν u T hT)

/-- Exact finite-time dissipation, retaining the physical H1 trace at T. -/
theorem heatTrajectory_laplacian_sq_integral
    (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2) =
      (2 * (ν : ℝ))⁻¹ *
        (physicalH1Enstrophy u - physicalH1Enstrophy (heatH1 ν T.toNNReal u)) := by
  rw [intervalIntegral.integral_of_le hT]
  calc
    (∫ t in Ioc (0 : ℝ) T, ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2) =
        ∫ t in Ioc (0 : ℝ) T, ∫ ξ : Space, heatDissipationDensity ν u t ξ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact heatTrajectory_laplacian_norm_sq_eq_integral ν hν u ht.1
    _ = _ := integral_heatDissipationDensity_space_time ν hν u T hT

/-- Native free-heat enstrophy-dissipation identity with the exact factor 2ν. -/
theorem heatTrajectory_enstrophy_dissipation
    (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    2 * (ν : ℝ) *
        (∫ t in (0 : ℝ)..T, ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2) =
      physicalH1Enstrophy u - physicalH1Enstrophy (heatH1 ν T.toNNReal u) := by
  have hc : 2 * (ν : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt hν)
  rw [heatTrajectory_laplacian_sq_integral ν hν u T hT, ← mul_assoc,
    mul_inv_cancel₀ hc, one_mul]

theorem heatTrajectory_laplacian_sq_integral_le
    (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2) ≤
      physicalH1Enstrophy u / (2 * (ν : ℝ)) := by
  rw [heatTrajectory_laplacian_sq_integral ν hν u T hT]
  calc
    (2 * (ν : ℝ))⁻¹ *
        (physicalH1Enstrophy u - physicalH1Enstrophy (heatH1 ν T.toNNReal u)) ≤
        (2 * (ν : ℝ))⁻¹ * physicalH1Enstrophy u :=
      mul_le_mul_of_nonneg_left
        (sub_le_self _ (physicalH1Enstrophy_nonneg _))
        (inv_nonneg.mpr (mul_nonneg (by norm_num) ν.property))
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

/-- The full inhomogeneous physical H2 norm is square integrable on every
finite time window, including arbitrarily small positive times. -/
theorem heatTrajectory_norm_sq_integrableOn
    (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    IntegrableOn (fun t : ℝ => ‖heatTrajectory ν hν u t‖ ^ 2)
      (Ioc (0 : ℝ) T) volume := by
  have hconst : IntegrableOn (fun _ : ℝ => ‖u‖ ^ 2) (Ioc (0 : ℝ) T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
      ((continuous_const : Continuous (fun _ : ℝ => ‖u‖ ^ 2)).intervalIntegrable 0 T)
  apply (hconst.add (heatTrajectory_laplacian_sq_integrableOn ν hν u T hT)).mono'
    ((heatTrajectory_stronglyMeasurable ν hν u).norm.pow 2).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact heatTrajectory_norm_sq_le ν hν u t

/-- An actual `MemLp 2` statement in the complete physical H2 space. -/
theorem heatTrajectory_memLp_two
    (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    MemLp (heatTrajectory ν hν u) 2 (volume.restrict (Ioc (0 : ℝ) T)) :=
  (memLp_two_iff_integrable_sq_norm
    (heatTrajectory_stronglyMeasurable ν hν u).aestronglyMeasurable).mpr
      (heatTrajectory_norm_sq_integrableOn ν hν u T hT)

/-- Quantitative finite-window H2 control uses the exact dissipated
enstrophy, never the nonintegrable pointwise `1/t` upper bound. -/
theorem heatTrajectory_norm_sq_integral_le
    (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖heatTrajectory ν hν u t‖ ^ 2) ≤
      T * ‖u‖ ^ 2 + physicalH1Enstrophy u / (2 * (ν : ℝ)) := by
  have hnorm : IntervalIntegrable (fun t : ℝ => ‖heatTrajectory ν hν u t‖ ^ 2)
      volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
      (heatTrajectory_norm_sq_integrableOn ν hν u T hT)
  have hconst : IntervalIntegrable (fun _ : ℝ => ‖u‖ ^ 2) volume 0 T :=
    (continuous_const : Continuous (fun _ : ℝ => ‖u‖ ^ 2)).intervalIntegrable 0 T
  have hlap := heatTrajectory_laplacian_sq_intervalIntegrable ν hν u T hT
  calc
    (∫ t in (0 : ℝ)..T, ‖heatTrajectory ν hν u t‖ ^ 2) ≤
        ∫ t in (0 : ℝ)..T,
          (‖u‖ ^ 2 + ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2) :=
      intervalIntegral.integral_mono_on hT hnorm (hconst.add hlap)
        (fun t _ => heatTrajectory_norm_sq_le ν hν u t)
    _ = T * ‖u‖ ^ 2 +
        ∫ t in (0 : ℝ)..T, ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2 := by
      rw [intervalIntegral.integral_add hconst hlap, intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
    _ ≤ _ := add_le_add le_rfl (heatTrajectory_laplacian_sq_integral_le ν hν u T hT)

end MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy
