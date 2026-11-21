import MethbokeAddon.QuasiFeffermanA.HeatSemigroup
import MethbokeAddon.QuasiFeffermanA.H2Spectral

/-!
# Positive-time smoothing into the actual physical H2 graph

At positive viscosity and time, bounded real even second-derivative symbols
construct all nine actual L2 Hessian entries. The reverse first-derivative
Fourier theorem identifies those entries as weak derivatives of the already
constructed heat gradients. Thus no H2 witness or smoothing estimate is an
input premise. The exact physical Laplacian has its literal heat multiplier.

The estimate `norm (Delta heat u)^2 <= (nu*t)^(-1) * norm (grad u)^2`
retains the physical Fourier normalization and suffices for the bounded
H1-to-H2 map. Its numerical constant is deliberately nonoptimal. This is a
positive-time spatial theorem; the time-integrated estimate and heat time
derivative are separate subsequent endpoints.

Prepared source requires matching authorized external compiler and independent
literal type/axiom evidence. No local Lean, Lake, or kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform NNReal Topology

namespace MethbokeAddon.QuasiFeffermanA.HeatSmoothing

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open HeatSemigroup RealEvenMultipliers

/-- Physical nonnegative Laplacian frequency in the `2*pi` convention. -/
def heatRate (ξ : Space) : ℝ := (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2

theorem heatRate_nonneg (ξ : Space) : 0 ≤ heatRate ξ := by
  unfold heatRate
  positivity

private theorem heatValue_eq_exp_rate (ν t : ℝ≥0) (ξ : Space) :
    heatValue ν t ξ = Real.exp (-((ν : ℝ) * (t : ℝ) * heatRate ξ)) := by
  unfold heatValue heatRate
  congr 1
  ring

/-- A literal positive-time multiplier bound, with no spectral assumption. -/
theorem heatRate_mul_heatValue_le (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (ξ : Space) :
    heatRate ξ * heatValue ν t ξ ≤ ((ν : ℝ) * (t : ℝ))⁻¹ := by
  have hprod : 0 < (ν : ℝ) * (t : ℝ) := mul_pos hν ht
  have hbound : ((ν : ℝ) * (t : ℝ)) * (heatRate ξ * heatValue ν t ξ) ≤ 1 := by
    rw [heatValue_eq_exp_rate]
    calc
      ((ν : ℝ) * (t : ℝ)) *
          (heatRate ξ * Real.exp (-((ν : ℝ) * (t : ℝ) * heatRate ξ))) =
          ((ν : ℝ) * (t : ℝ) * heatRate ξ) *
            Real.exp (-((ν : ℝ) * (t : ℝ) * heatRate ξ)) := by ring
      _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one _
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  apply (mul_le_mul_iff_left₀ hprod).mp
  simpa only [mul_inv_cancel₀ (ne_of_gt hprod)] using hbound

private theorem heatRate_mul_heatValue_sq_le (ν t : ℝ≥0)
    (hν : 0 < ν) (ht : 0 < t) (ξ : Space) :
    heatRate ξ * (heatValue ν t ξ) ^ 2 ≤ ((ν : ℝ) * (t : ℝ))⁻¹ := by
  calc
    heatRate ξ * (heatValue ν t ξ) ^ 2 =
        (heatRate ξ * heatValue ν t ξ) * heatValue ν t ξ := by ring
    _ ≤ heatRate ξ * heatValue ν t ξ :=
      mul_le_of_le_one_right
        (mul_nonneg (heatRate_nonneg ξ) (heatValue_pos ν t ξ).le)
        (heatValue_le_one ν t ξ)
    _ ≤ _ := heatRate_mul_heatValue_le ν t hν ht ξ

/-- The literal ordered second-derivative heat symbol. -/
def heatHessianValue (ν t : ℝ≥0) (j k : Fin 3) (ξ : Space) : ℝ :=
  -((2 * Real.pi) ^ 2) * ξ j * ξ k * heatValue ν t ξ

theorem heatHessianValue_continuous (ν t : ℝ≥0) (j k : Fin 3) :
    Continuous (heatHessianValue ν t j k) := by
  unfold heatHessianValue heatValue
  fun_prop

theorem heatHessianValue_even (ν t : ℝ≥0) (j k : Fin 3) (ξ : Space) :
    heatHessianValue ν t j k (-ξ) = heatHessianValue ν t j k ξ := by
  change -((2 * Real.pi) ^ 2) * (-ξ j) * (-ξ k) * heatValue ν t (-ξ) =
    -((2 * Real.pi) ^ 2) * ξ j * ξ k * heatValue ν t ξ
  rw [heatValue_neg]
  ring

private theorem abs_coordinate_le_norm (ξ : Space) (j : Fin 3) :
    |ξ j| ≤ ‖ξ‖ := by
  have hsq : (ξ j) ^ 2 ≤ ‖ξ‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (ξ k)) (Finset.mem_univ j)
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  simpa only [sq_abs] using hsq

theorem heatHessianValue_norm_le (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (j k : Fin 3) (ξ : Space) :
    ‖heatHessianValue ν t j k ξ‖ ≤ ((ν : ℝ) * (t : ℝ))⁻¹ := by
  rw [Real.norm_eq_abs, heatHessianValue, abs_mul, abs_mul, abs_mul,
    abs_neg, abs_of_nonneg (sq_nonneg _), abs_of_pos (heatValue_pos ν t ξ)]
  have hheat : 0 ≤ heatValue ν t ξ := (heatValue_pos ν t ξ).le
  calc
    (2 * Real.pi) ^ 2 * |ξ j| * |ξ k| * heatValue ν t ξ ≤
        (2 * Real.pi) ^ 2 * ‖ξ‖ * ‖ξ‖ * heatValue ν t ξ := by
      gcongr
      · exact abs_coordinate_le_norm ξ j
      · exact abs_coordinate_le_norm ξ k
    _ = heatRate ξ * heatValue ν t ξ := by unfold heatRate; ring
    _ ≤ _ := heatRate_mul_heatValue_le ν t hν ht ξ

/-- The bounded measurable real-even symbol is constructed at positive times. -/
def heatHessianSymbol (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (j k : Fin 3) : RealEvenSymbol where
  value := heatHessianValue ν t j k
  measurable := (heatHessianValue_continuous ν t j k).measurable
  even := heatHessianValue_even ν t j k
  bound := (ν * t)⁻¹
  norm_le := fun ξ => by
    simpa only [NNReal.coe_inv, NNReal.coe_mul] using
      heatHessianValue_norm_le ν t hν ht j k ξ

/-- Actual real L2 Hessian output, without a supplied derivative witness. -/
def heatHessianL2 (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (j k : Fin 3) (v : SpatialL2) : SpatialL2 :=
  realFourierMultiplier (heatHessianSymbol ν t hν ht j k) v

theorem heatHessianL2_fourier_ae (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (j k : Fin 3) (v : SpatialL2) :
    (fun ξ : Space => (𝓕 (complexifyL2 (heatHessianL2 ν t hν ht j k v)) : ComplexL2) ξ)
      =ᵐ[volume] (fun ξ : Space =>
        (heatHessianValue ν t j k ξ : ℂ) • (𝓕 (complexifyL2 v) : ComplexL2) ξ) :=
  fourier_complexify_realFourierMultiplier_ae (heatHessianSymbol ν t hν ht j k) v

theorem norm_heatHessianL2_le (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (j k : Fin 3) (v : SpatialL2) :
    ‖heatHessianL2 ν t hν ht j k v‖ ≤ ((ν : ℝ) * (t : ℝ))⁻¹ * ‖v‖ := by
  simpa only [heatHessianL2, heatHessianSymbol, NNReal.coe_inv, NNReal.coe_mul] using
    norm_realFourierMultiplier_le (heatHessianSymbol ν t hν ht j k) v

private theorem coordinate_inner (ξ : Space) (j : Fin 3) :
    inner ℝ ξ (coordinateVector j) = ξ j := by
  simpa only [coordinateVector, EuclideanSpace.basisFun_apply] using
    EuclideanSpace.inner_basisFun_real (Fin 3) ξ j

private theorem heatHessianValue_complex_eq (ν t : ℝ≥0)
    (j k : Fin 3) (ξ : Space) :
    (heatHessianValue ν t j k ξ : ℂ) =
      ((2 * Real.pi * Complex.I) * (inner ℝ ξ (coordinateVector k) : ℂ)) *
        ((heatValue ν t ξ : ℂ) *
          ((2 * Real.pi * Complex.I) * (inner ℝ ξ (coordinateVector j) : ℂ))) := by
  rw [coordinate_inner, coordinate_inner]
  simp only [heatHessianValue, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  calc
    _ = ((2 * (Real.pi : ℂ)) ^ 2 * (ξ j : ℂ) * (ξ k : ℂ) *
        (heatValue ν t ξ : ℂ)) * Complex.I ^ 2 := by rw [Complex.I_sq]; ring
    _ = _ := by ring

/-- The constructed nine L2 fields are the actual weak derivatives of the
constructed heat gradients, by the reverse Fourier derivative theorem. -/
theorem spatialWeakHessian_heatL2 (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    {v : SpatialL2} {G : Fin 3 → SpatialL2} (hG : SpatialWeakGradient v G) :
    SpatialWeakHessian (fun j => heatL2 ν t (G j))
      (fun j k => heatHessianL2 ν t hν ht j k v) := by
  intro j
  apply (H1Fourier.spatialWeakGradient_iff_fourier_ae _ _).mpr
  have hH : ∀ᵐ ξ : Space ∂volume, ∀ k : Fin 3,
      (𝓕 (complexifyL2 (heatHessianL2 ν t hν ht j k v)) : ComplexL2) ξ =
        (heatHessianValue ν t j k ξ : ℂ) • (𝓕 (complexifyL2 v) : ComplexL2) ξ :=
    ae_all_iff.mpr (fun k => heatHessianL2_fourier_ae ν t hν ht j k v)
  filter_upwards [hH, heatL2_fourier_ae ν t (G j),
    H1Fourier.spatialWeakGradient_fourier_ae hG] with ξ hh hg hgrad
  intro k
  rw [hh k, hg, hgrad j, heatHessianValue_complex_eq]
  simp only [smul_smul, mul_assoc]

/-- Positive time constructs an actual physical H2 element from arbitrary H1 data. -/
def heatH1ToH2 (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (u : PhysicalH1) : PhysicalH2 :=
  physicalH2OfWeakDerivatives (heatL2 ν t (physicalH1Velocity u))
    (fun j => heatL2 ν t (physicalH1Gradient j u))
    (fun j k => heatHessianL2 ν t hν ht j k (physicalH1Velocity u))
    (spatialWeakGradient_heatL2 ν t (physicalH1_weakGradient u))
    (spatialWeakHessian_heatL2 ν t hν ht (physicalH1_weakGradient u))

@[simp] theorem heatH1ToH2_velocity (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (u : PhysicalH1) :
    physicalH2Velocity (heatH1ToH2 ν t hν ht u) = heatL2 ν t (physicalH1Velocity u) := rfl

@[simp] theorem heatH1ToH2_gradient (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (u : PhysicalH1) (j : Fin 3) :
    physicalH2Gradient j (heatH1ToH2 ν t hν ht u) =
      heatL2 ν t (physicalH1Gradient j u) := rfl

@[simp] theorem heatH1ToH2_hessian (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (u : PhysicalH1) (j k : Fin 3) :
    physicalH2Hessian j k (heatH1ToH2 ν t hν ht u) =
      heatHessianL2 ν t hν ht j k (physicalH1Velocity u) := rfl

/-- The constructed H2 element has exactly the previously constructed H1 heat trace. -/
theorem heatH1ToH2_toH1 (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (u : PhysicalH1) : physicalH2ToH1 (heatH1ToH2 ν t hν ht u) = heatH1 ν t u := by
  apply physicalH1Velocity_injective
  simp only [physicalH2ToH1_velocity, heatH1ToH2_velocity, heatH1_velocity]

/-- The actual graph Laplacian has the literal negative heat-rate multiplier. -/
theorem heatH1ToH2_laplacian_fourier_ae (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (u : PhysicalH1) :
    (fun ξ : Space =>
      (𝓕 (complexifyL2 (physicalH2Laplacian (heatH1ToH2 ν t hν ht u))) : ComplexL2) ξ)
      =ᵐ[volume] (fun ξ : Space =>
        ((-heatRate ξ * heatValue ν t ξ : ℝ) : ℂ) •
          (𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ) := by
  filter_upwards [H2Spectral.physicalH2_laplacian_fourier_ae (heatH1ToH2 ν t hν ht u),
    heatL2_fourier_ae ν t (physicalH1Velocity u)] with ξ hΔ hheat
  rw [hΔ, heatH1ToH2_velocity, hheat, smul_smul]
  congr 1
  simp only [heatRate, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

/-- Positive-time Laplacian smoothing is controlled by the original physical
gradient only. The constant one is sufficient and is not claimed optimal. -/
theorem heatH1ToH2_laplacian_norm_sq_le (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (u : PhysicalH1) :
    ‖physicalH2Laplacian (heatH1ToH2 ν t hν ht u)‖ ^ 2 ≤
      ((ν : ℝ) * (t : ℝ))⁻¹ * physicalH1Enstrophy u := by
  rw [H2Spectral.physicalH2_laplacian_norm_sq_eq_fourier]
  have hA := H2Spectral.physicalH2_fourier_laplacian_integrable (heatH1ToH2 ν t hν ht u)
  have hB := (H1Spectral.integrable_fourier_gradient (physicalH1_weakGradient u)).const_mul
    (((ν : ℝ) * (t : ℝ))⁻¹)
  calc
    (∫ ξ : Space, (2 * Real.pi) ^ 4 * ‖ξ‖ ^ 4 *
        ‖(𝓕 (complexifyL2 (physicalH2Velocity (heatH1ToH2 ν t hν ht u))) : ComplexL2) ξ‖ ^ 2) ≤
        ∫ ξ : Space, ((ν : ℝ) * (t : ℝ))⁻¹ *
          ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
            ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) := by
      apply integral_mono_ae hA hB
      filter_upwards [heatL2_fourier_ae ν t (physicalH1Velocity u)] with ξ hξ
      rw [heatH1ToH2_velocity, hξ, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (heatValue_pos ν t ξ)]
      have hb := mul_le_mul_of_nonneg_right (heatRate_mul_heatValue_sq_le ν t hν ht ξ)
        (mul_nonneg (heatRate_nonneg ξ)
          (sq_nonneg ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖))
      convert hb using 1 <;> dsimp only [heatRate] <;> ring
    _ = ((ν : ℝ) * (t : ℝ))⁻¹ * physicalH1Enstrophy u := by
      rw [integral_const_mul, H1Spectral.integral_fourier_gradient (physicalH1_weakGradient u)]
      rfl

/-- Exact inhomogeneous H2 control retains the original velocity norm. -/
theorem heatH1ToH2_norm_sq_le_energy_enstrophy
    (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) :
    ‖heatH1ToH2 ν t hν ht u‖ ^ 2 ≤
      ‖u‖ ^ 2 + ((ν : ℝ) * (t : ℝ))⁻¹ * physicalH1Enstrophy u := by
  rw [H2Spectral.physicalH2_norm_sq_eq_laplacian, physicalH1_norm_sq]
  exact add_le_add
    (add_le_add (heatH1_energy_le ν t u) (heatH1_enstrophy_le ν t u))
    (heatH1ToH2_laplacian_norm_sq_le ν t hν ht u)

theorem heatH1ToH2_norm_sq_le (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (u : PhysicalH1) :
    ‖heatH1ToH2 ν t hν ht u‖ ^ 2 ≤
      (1 + ((ν : ℝ) * (t : ℝ))⁻¹) * ‖u‖ ^ 2 := by
  calc
    ‖heatH1ToH2 ν t hν ht u‖ ^ 2 ≤
        ‖u‖ ^ 2 + ((ν : ℝ) * (t : ℝ))⁻¹ * physicalH1Enstrophy u :=
      heatH1ToH2_norm_sq_le_energy_enstrophy ν t hν ht u
    _ ≤ ‖u‖ ^ 2 + ((ν : ℝ) * (t : ℝ))⁻¹ * ‖u‖ ^ 2 := by
      have hinv : 0 ≤ ((ν : ℝ) * (t : ℝ))⁻¹ :=
        inv_nonneg.mpr (mul_nonneg ν.property t.property)
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left (physicalH1Enstrophy_le_norm_sq u) hinv) _
    _ = _ := by ring

theorem norm_heatH1ToH2_le (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (u : PhysicalH1) :
    ‖heatH1ToH2 ν t hν ht u‖ ≤
      Real.sqrt (1 + ((ν : ℝ) * (t : ℝ))⁻¹) * ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact heatH1ToH2_norm_sq_le ν t hν ht u

theorem heatH1ToH2_add (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (u v : PhysicalH1) :
    heatH1ToH2 ν t hν ht (u + v) = heatH1ToH2 ν t hν ht u + heatH1ToH2 ν t hν ht v := by
  apply physicalH2Velocity_injective
  simp only [heatH1ToH2_velocity, map_add, heatL2_add]

theorem heatH1ToH2_smul (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (r : ℝ) (u : PhysicalH1) :
    heatH1ToH2 ν t hν ht (r • u) = r • heatH1ToH2 ν t hν ht u := by
  apply physicalH2Velocity_injective
  simp only [heatH1ToH2_velocity, map_smul, heatL2_smul]

/-- The concrete positive-time bounded linear map into actual physical H2. -/
def heatH1ToH2CLM (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) :
    PhysicalH1 →L[ℝ] PhysicalH2 :=
  ({ toFun := heatH1ToH2 ν t hν ht
     map_add' := heatH1ToH2_add ν t hν ht
     map_smul' := heatH1ToH2_smul ν t hν ht } : PhysicalH1 →ₗ[ℝ] PhysicalH2).mkContinuous
    (Real.sqrt (1 + ((ν : ℝ) * (t : ℝ))⁻¹))
    (norm_heatH1ToH2_le ν t hν ht)

@[simp] theorem heatH1ToH2CLM_apply (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (u : PhysicalH1) : heatH1ToH2CLM ν t hν ht u = heatH1ToH2 ν t hν ht u := rfl

end MethbokeAddon.QuasiFeffermanA.HeatSmoothing
