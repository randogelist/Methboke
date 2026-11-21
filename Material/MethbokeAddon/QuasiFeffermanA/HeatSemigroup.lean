import MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers
import MethbokeAddon.QuasiFeffermanA.H1Spectral
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The actual real Fourier heat semigroup on L2 and physical H1

The literal symbol `exp (-(4*pi^2*nu*t*norm xi^2))` constructs an actual
bounded real Fourier operator, including zero viscosity and zero time.
Fourier injectivity proves the semigroup law. Dominated convergence against
the input's genuine integrable Fourier energy proves strong continuity.
Applying the same operator to supplied physical gradients constructs the
native H1 lift, with its full inhomogeneous norm and strong continuity.

No higher derivative, time-dependent forcing, nonlinear evolution or
canonical NSE existence premise is introduced. Positive-time H2 smoothing
and the forced heat equation remain subsequent constructions.

Prepared source requires matching external compilation and complete named
type/axiom evidence. No local Lean, Lake or kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory FourierTransform Filter
open scoped BigOperators FourierTransform NNReal Topology

namespace MethbokeAddon.QuasiFeffermanA.HeatSemigroup

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open RealEvenMultipliers

/-- Literal heat symbol in the physical `exp(-2*pi*i*x.xi)` convention. -/
def heatValue (ν t : ℝ≥0) (ξ : Space) : ℝ :=
  Real.exp (-(4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ) * ‖ξ‖ ^ 2))

theorem heatValue_pos (ν t : ℝ≥0) (ξ : Space) : 0 < heatValue ν t ξ :=
  Real.exp_pos _

theorem heatValue_le_one (ν t : ℝ≥0) (ξ : Space) : heatValue ν t ξ ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (by positivity)

theorem heatValue_continuous_frequency (ν t : ℝ≥0) : Continuous (heatValue ν t) := by
  unfold heatValue
  fun_prop

theorem heatValue_continuous_time (ν : ℝ≥0) (ξ : Space) :
    Continuous (fun t : ℝ≥0 => heatValue ν t ξ) := by
  unfold heatValue
  fun_prop

@[simp] theorem heatValue_neg (ν t : ℝ≥0) (ξ : Space) :
    heatValue ν t (-ξ) = heatValue ν t ξ := by simp only [heatValue, norm_neg]

@[simp] theorem heatValue_zero_time (ν : ℝ≥0) (ξ : Space) :
    heatValue ν 0 ξ = 1 := by simp [heatValue]

@[simp] theorem heatValue_zero_viscosity (t : ℝ≥0) (ξ : Space) :
    heatValue 0 t ξ = 1 := by simp [heatValue]

theorem heatValue_add_time (ν s t : ℝ≥0) (ξ : Space) :
    heatValue ν (s + t) ξ = heatValue ν s ξ * heatValue ν t ξ := by
  simp only [heatValue, NNReal.coe_add]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The symbol data are proved for the literal heat function, with bound one. -/
def heatSymbol (ν t : ℝ≥0) : RealEvenSymbol where
  value := heatValue ν t
  measurable := (heatValue_continuous_frequency ν t).measurable
  even := heatValue_neg ν t
  bound := 1
  norm_le := fun ξ => by
    change ‖heatValue ν t ξ‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (heatValue_pos ν t ξ)]
    exact heatValue_le_one ν t ξ

@[simp] theorem heatSymbol_value (ν t : ℝ≥0) (ξ : Space) :
    (heatSymbol ν t).value ξ =
      Real.exp (-(4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ) * ‖ξ‖ ^ 2)) := rfl

/-- Actual real full-volume L2 heat evolution, constructed from its even symbol. -/
def heatL2 (ν t : ℝ≥0) (u : SpatialL2) : SpatialL2 :=
  realFourierMultiplier (heatSymbol ν t) u

def heatL2CLM (ν t : ℝ≥0) : SpatialL2 →L[ℝ] SpatialL2 :=
  realFourierMultiplierCLM (heatSymbol ν t)

@[simp] theorem heatL2CLM_apply (ν t : ℝ≥0) (u : SpatialL2) :
    heatL2CLM ν t u = heatL2 ν t u := rfl

/-- The Fourier formula concerns the constructed physical real L2 class. -/
theorem heatL2_fourier_ae (ν t : ℝ≥0) (u : SpatialL2) :
    (fun ξ : Space => (𝓕 (complexifyL2 (heatL2 ν t u)) : ComplexL2) ξ)
      =ᵐ[volume] (fun ξ : Space =>
        (heatValue ν t ξ : ℂ) • (𝓕 (complexifyL2 u) : ComplexL2) ξ) :=
  fourier_complexify_realFourierMultiplier_ae (heatSymbol ν t) u

theorem heatL2_add (ν t : ℝ≥0) (u v : SpatialL2) :
    heatL2 ν t (u + v) = heatL2 ν t u + heatL2 ν t v :=
  (heatL2CLM ν t).map_add u v

theorem heatL2_smul (ν t : ℝ≥0) (r : ℝ) (u : SpatialL2) :
    heatL2 ν t (r • u) = r • heatL2 ν t u :=
  (heatL2CLM ν t).map_smul r u

@[simp] theorem heatL2_zero (ν t : ℝ≥0) : heatL2 ν t 0 = 0 :=
  (heatL2CLM ν t).map_zero

theorem norm_heatL2_le (ν t : ℝ≥0) (u : SpatialL2) :
    ‖heatL2 ν t u‖ ≤ ‖u‖ := by
  simpa only [heatL2, heatSymbol, NNReal.coe_one, one_mul] using
    norm_realFourierMultiplier_le (heatSymbol ν t) u

@[simp] theorem heatL2_zero_time (ν : ℝ≥0) (u : SpatialL2) :
    heatL2 ν 0 u = u := by
  symm
  apply realFourierMultiplier_eq_of_fourier_ae (heatSymbol ν 0) u u
  filter_upwards with ξ
  simp only [heatSymbol, heatValue_zero_time, Complex.ofReal_one, one_smul]

@[simp] theorem heatL2_zero_viscosity (t : ℝ≥0) (u : SpatialL2) :
    heatL2 0 t u = u := by
  symm
  apply realFourierMultiplier_eq_of_fourier_ae (heatSymbol 0 t) u u
  filter_upwards with ξ
  simp only [heatSymbol, heatValue_zero_viscosity, Complex.ofReal_one, one_smul]

/-- The actual real L2 semigroup law, including all zero cases. -/
theorem heatL2_add_time (ν s t : ℝ≥0) (u : SpatialL2) :
    heatL2 ν (s + t) u = heatL2 ν s (heatL2 ν t u) := by
  symm
  apply realFourierMultiplier_eq_of_fourier_ae (heatSymbol ν (s + t)) u
    (heatL2 ν s (heatL2 ν t u))
  filter_upwards [heatL2_fourier_ae ν s (heatL2 ν t u), heatL2_fourier_ae ν t u]
    with ξ hs ht
  rw [hs, ht, smul_smul]
  change ((heatValue ν s ξ : ℂ) * (heatValue ν t ξ : ℂ)) •
      (𝓕 (complexifyL2 u) : ComplexL2) ξ =
    (heatValue ν (s + t) ξ : ℂ) • (𝓕 (complexifyL2 u) : ComplexL2) ξ
  rw [heatValue_add_time, Complex.ofReal_mul]

private theorem fourier_complexify_sub (u v : SpatialL2) :
    (𝓕 (complexifyL2 (u - v)) : ComplexL2) =
      (𝓕 (complexifyL2 u) : ComplexL2) - (𝓕 (complexifyL2 v) : ComplexL2) := by
  change (Lp.fourierTransformₗᵢ Space ComplexVector) (complexifyL2LI (u - v)) =
    (Lp.fourierTransformₗᵢ Space ComplexVector) (complexifyL2LI u) -
      (Lp.fourierTransformₗᵢ Space ComplexVector) (complexifyL2LI v)
  rw [map_sub, map_sub]

/-- Exact actual L2 distance is the integral of the squared literal symbol
difference against the input's Fourier energy. -/
theorem heatL2_sub_norm_sq_eq_fourier (ν t s : ℝ≥0) (u : SpatialL2) :
    ‖heatL2 ν t u - heatL2 ν s u‖ ^ 2 =
      ∫ ξ : Space, (heatValue ν t ξ - heatValue ν s ξ) ^ 2 *
        ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2 := by
  calc
    ‖heatL2 ν t u - heatL2 ν s u‖ ^ 2 =
        ∫ ξ : Space,
          ‖(𝓕 (complexifyL2 (heatL2 ν t u - heatL2 ν s u)) : ComplexL2) ξ‖ ^ 2 :=
      (H1Spectral.integral_fourier_energy _).symm
    _ = _ := by
      rw [fourier_complexify_sub]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub
        (𝓕 (complexifyL2 (heatL2 ν t u)) : ComplexL2)
        (𝓕 (complexifyL2 (heatL2 ν s u)) : ComplexL2),
        heatL2_fourier_ae ν t u, heatL2_fourier_ae ν s u] with ξ hsub ht hs
      rw [hsub, Pi.sub_apply, ht, hs, ← sub_smul, ← Complex.ofReal_sub,
        norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem heatValue_sub_sq_le_one (ν t s : ℝ≥0) (ξ : Space) :
    (heatValue ν t ξ - heatValue ν s ξ) ^ 2 ≤ 1 := by
  apply (sq_le_one_iff_abs_le_one _).mpr
  apply abs_le.mpr
  constructor <;> linarith [heatValue_pos ν t ξ, heatValue_pos ν s ξ,
    heatValue_le_one ν t ξ, heatValue_le_one ν s ξ]

private theorem continuous_integral_heat_difference (ν s : ℝ≥0) (u : SpatialL2) :
    Continuous (fun t : ℝ≥0 => ∫ ξ : Space,
      (heatValue ν t ξ - heatValue ν s ξ) ^ 2 *
        ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2) := by
  apply continuous_of_dominated
    (bound := fun ξ : Space => ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2)
  · intro t
    exact (((heatValue_continuous_frequency ν t).aestronglyMeasurable.sub
      (heatValue_continuous_frequency ν s).aestronglyMeasurable).pow 2).mul
        ((Lp.aestronglyMeasurable (𝓕 (complexifyL2 u) : ComplexL2)).norm.pow 2)
  · intro t
    filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact (mul_le_mul_of_nonneg_right (heatValue_sub_sq_le_one ν t s ξ)
      (sq_nonneg _)).trans_eq (one_mul _)
  · exact H1Spectral.integrable_fourier_energy u
  · filter_upwards with ξ
    exact (((heatValue_continuous_time ν ξ).sub continuous_const).pow 2).mul
      continuous_const

private theorem continuous_of_squared_distances
    {E : Type*} [NormedAddCommGroup E] (f : ℝ≥0 → E)
    (h : ∀ s : ℝ≥0, Continuous (fun t : ℝ≥0 => ‖f t - f s‖ ^ 2)) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq : Tendsto (fun t : ℝ≥0 => ‖f t - f s‖ ^ 2) (𝓝 s) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (h s).tendsto s
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

/-- Strong continuity is proved against an integrable Fourier-energy
majorant. It includes continuity at the initial time and zero viscosity. -/
theorem heatL2_continuous (ν : ℝ≥0) (u : SpatialL2) :
    Continuous (fun t : ℝ≥0 => heatL2 ν t u) := by
  apply continuous_of_squared_distances
  intro s
  simpa only [heatL2_sub_norm_sq_eq_fourier] using
    continuous_integral_heat_difference ν s u

/-- The actual supplied weak gradients commute with the heat operator. -/
theorem spatialWeakGradient_heatL2 (ν t : ℝ≥0)
    {v : SpatialL2} {G : Fin 3 → SpatialL2} (h : SpatialWeakGradient v G) :
    SpatialWeakGradient (heatL2 ν t v) (fun j => heatL2 ν t (G j)) :=
  spatialWeakGradient_realFourierMultiplier (heatSymbol ν t) h

/-- Native physical H1 heat evolution uses the actual projected velocity
and all three actual projected weak-gradient fields. -/
def heatH1 (ν t : ℝ≥0) (u : PhysicalH1) : PhysicalH1 :=
  physicalH1OfWeakGradient (heatL2 ν t (physicalH1Velocity u))
    (fun j => heatL2 ν t (physicalH1Gradient j u))
    (spatialWeakGradient_heatL2 ν t (physicalH1_weakGradient u))

@[simp] theorem heatH1_velocity (ν t : ℝ≥0) (u : PhysicalH1) :
    physicalH1Velocity (heatH1 ν t u) = heatL2 ν t (physicalH1Velocity u) := rfl

@[simp] theorem heatH1_gradient (ν t : ℝ≥0) (u : PhysicalH1) (j : Fin 3) :
    physicalH1Gradient j (heatH1 ν t u) = heatL2 ν t (physicalH1Gradient j u) := rfl

theorem heatH1_add (ν t : ℝ≥0) (u v : PhysicalH1) :
    heatH1 ν t (u + v) = heatH1 ν t u + heatH1 ν t v := by
  apply physicalH1Velocity_injective
  simp only [heatH1_velocity, map_add, heatL2_add]

theorem heatH1_smul (ν t : ℝ≥0) (r : ℝ) (u : PhysicalH1) :
    heatH1 ν t (r • u) = r • heatH1 ν t u := by
  apply physicalH1Velocity_injective
  simp only [heatH1_velocity, map_smul, heatL2_smul]

@[simp] theorem heatH1_zero (ν t : ℝ≥0) : heatH1 ν t 0 = 0 := by
  apply physicalH1Velocity_injective
  simp only [heatH1_velocity, map_zero, heatL2_zero]

theorem heatH1_norm_sq_le (ν t : ℝ≥0) (u : PhysicalH1) :
    ‖heatH1 ν t u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [physicalH1_norm_sq, physicalH1_norm_sq]
  simp only [heatH1_velocity, heatH1_gradient]
  apply add_le_add
  · exact pow_le_pow_left₀ (norm_nonneg _) (norm_heatL2_le ν t _) 2
  · exact Finset.sum_le_sum (fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_heatL2_le ν t _) 2)

/-- Contraction retains both velocity and weak-gradient parts of the H1 norm. -/
theorem norm_heatH1_le (ν t : ℝ≥0) (u : PhysicalH1) :
    ‖heatH1 ν t u‖ ≤ ‖u‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (heatH1_norm_sq_le ν t u)

def heatH1CLM (ν t : ℝ≥0) : PhysicalH1 →L[ℝ] PhysicalH1 :=
  ({ toFun := heatH1 ν t
     map_add' := heatH1_add ν t
     map_smul' := heatH1_smul ν t } : PhysicalH1 →ₗ[ℝ] PhysicalH1).mkContinuous 1
    (fun u => by
      change ‖heatH1 ν t u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using norm_heatH1_le ν t u)

@[simp] theorem heatH1CLM_apply (ν t : ℝ≥0) (u : PhysicalH1) :
    heatH1CLM ν t u = heatH1 ν t u := rfl

@[simp] theorem heatH1_zero_time (ν : ℝ≥0) (u : PhysicalH1) :
    heatH1 ν 0 u = u := by
  apply physicalH1Velocity_injective
  simp only [heatH1_velocity, heatL2_zero_time]

@[simp] theorem heatH1_zero_viscosity (t : ℝ≥0) (u : PhysicalH1) :
    heatH1 0 t u = u := by
  apply physicalH1Velocity_injective
  simp only [heatH1_velocity, heatL2_zero_viscosity]

theorem heatH1_add_time (ν s t : ℝ≥0) (u : PhysicalH1) :
    heatH1 ν (s + t) u = heatH1 ν s (heatH1 ν t u) := by
  apply physicalH1Velocity_injective
  simp only [heatH1_velocity, heatL2_add_time]

theorem heatH1_energy_le (ν t : ℝ≥0) (u : PhysicalH1) :
    physicalH1Energy (heatH1 ν t u) ≤ physicalH1Energy u :=
  pow_le_pow_left₀ (norm_nonneg _) (norm_heatL2_le ν t _) 2

theorem heatH1_enstrophy_le (ν t : ℝ≥0) (u : PhysicalH1) :
    physicalH1Enstrophy (heatH1 ν t u) ≤ physicalH1Enstrophy u := by
  change (∑ j : Fin 3, ‖heatL2 ν t (physicalH1Gradient j u)‖ ^ 2) ≤
    ∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2
  exact Finset.sum_le_sum (fun j _ =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_heatL2_le ν t _) 2)

/-- Strong continuity in the actual complete inhomogeneous physical H1
graph, including its original initial value at time zero. -/
theorem heatH1_continuous (ν : ℝ≥0) (u : PhysicalH1) :
    Continuous (fun t : ℝ≥0 => heatH1 ν t u) := by
  apply continuous_of_squared_distances
  intro s
  have hv : Continuous (fun t : ℝ≥0 =>
      ‖heatL2 ν t (physicalH1Velocity u) - heatL2 ν s (physicalH1Velocity u)‖ ^ 2) :=
    ((heatL2_continuous ν (physicalH1Velocity u)).sub continuous_const).norm.pow 2
  have hG : Continuous (fun t : ℝ≥0 => ∑ j : Fin 3,
      ‖heatL2 ν t (physicalH1Gradient j u) - heatL2 ν s (physicalH1Gradient j u)‖ ^ 2) :=
    continuous_finsetSum Finset.univ (fun j _ =>
      ((heatL2_continuous ν (physicalH1Gradient j u)).sub continuous_const).norm.pow 2)
  have hsum := hv.add hG
  change Continuous (fun t : ℝ≥0 =>
    ‖heatL2 ν t (physicalH1Velocity u) - heatL2 ν s (physicalH1Velocity u)‖ ^ 2 +
      ∑ j : Fin 3,
        ‖heatL2 ν t (physicalH1Gradient j u) - heatL2 ν s (physicalH1Gradient j u)‖ ^ 2) at hsum
  simpa only [physicalH1_norm_sq, map_sub, heatH1_velocity, heatH1_gradient] using hsum

end MethbokeAddon.QuasiFeffermanA.HeatSemigroup
