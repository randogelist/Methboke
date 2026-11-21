import MethbokeAddon.R3Ehrenfest.SharpCutoff
import MethbokeAddon.QuasiFeffermanA.PhysicalH2
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Constructed derivatives and a physical H2 lift of the sharp Fourier cutoff

The first derivative symbols are imaginary and odd. They are not instances
of the real-even symbol interface. Their Hermitian symmetry is proved here,
and the existing real Fourier range theorem constructs actual real L2
derivatives. The reverse Fourier derivative theorem then proves the native
compact-test weak derivative identities. No derivative witness is assumed.

Applying the same bounded derivative operators a second time constructs the
actual physical H2 graph. The explicit component-count bound is sufficient
for a fixed-cutoff bounded lift; no sharp Bernstein or uniform nonlinear
comparison constant is claimed. Smooth representatives, the nonlinear vector
field and its trajectories remain separate constructions.

Prepared source requires matching authorized cached external compilation and
named type/axiom evidence. No local Lean, Lake or kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform NNReal

namespace MethbokeAddon.R3Ehrenfest.Bandlimited

open MethbokeAddon.QuasiFeffermanA
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open RealFourier
open MethbokeAddon.R3Ehrenfest.SharpCutoff

/- The bounded Hermitian scalar construction is kept internal. Its concrete
derivative instance below proves all of these elementary symbol properties. -/
private structure HermitianSymbol where
  value : Space → ℂ
  measurable : Measurable value
  reflected_conj : ∀ ξ : Space, conj (value (-ξ)) = value ξ
  bound : ℝ≥0
  norm_le : ∀ ξ : Space, ‖value ξ‖ ≤ (bound : ℝ)

private theorem memLp_hermitian_smul (m : HermitianSymbol) (f : ComplexL2) :
    MemLp (fun ξ : Space => m.value ξ • f ξ) 2 volume := by
  apply (Lp.memLp f).of_le_mul (c := (m.bound : ℝ))
    (m.measurable.aestronglyMeasurable.smul (Lp.aestronglyMeasurable f))
  filter_upwards with ξ
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (m.norm_le ξ) (norm_nonneg _)

private def frequencyAction (m : HermitianSymbol) (f : ComplexL2) : ComplexL2 :=
  (memLp_hermitian_smul m f).toLp (fun ξ : Space => m.value ξ • f ξ)

private theorem frequencyAction_ae (m : HermitianSymbol) (f : ComplexL2) :
    (fun ξ : Space => frequencyAction m f ξ) =ᵐ[volume]
      (fun ξ : Space => m.value ξ • f ξ) := MemLp.coeFn_toLp _

private theorem norm_frequencyAction_le (m : HermitianSymbol) (f : ComplexL2) :
    ‖frequencyAction m f‖ ≤ (m.bound : ℝ) * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [frequencyAction_ae m f] with ξ hξ
  rw [hξ, norm_smul]
  exact mul_le_mul_of_nonneg_right (m.norm_le ξ) (norm_nonneg _)

private theorem frequencyAction_add (m : HermitianSymbol) (f g : ComplexL2) :
    frequencyAction m (f + g) = frequencyAction m f + frequencyAction m g := by
  apply Lp.ext
  filter_upwards [frequencyAction_ae m (f + g), frequencyAction_ae m f,
    frequencyAction_ae m g, Lp.coeFn_add f g,
    Lp.coeFn_add (frequencyAction m f) (frequencyAction m g)]
    with ξ hsum hf hg hadd htarget
  rw [hsum, htarget, Pi.add_apply, hadd, Pi.add_apply, hf, hg, smul_add]

private theorem frequencyAction_smul (m : HermitianSymbol) (c : ℂ) (f : ComplexL2) :
    frequencyAction m (c • f) = c • frequencyAction m f := by
  apply Lp.ext
  filter_upwards [frequencyAction_ae m (c • f), frequencyAction_ae m f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (frequencyAction m f)]
    with ξ hscaled hf hsource htarget
  rw [hscaled, htarget, Pi.smul_apply, hsource, Pi.smul_apply, hf]
  exact smul_comm _ _ _

private def frequencyActionCLM (m : HermitianSymbol) : ComplexL2 →L[ℂ] ComplexL2 :=
  ({ toFun := frequencyAction m
     map_add' := frequencyAction_add m
     map_smul' := frequencyAction_smul m } : ComplexL2 →ₗ[ℂ] ComplexL2).mkContinuous
      (m.bound : ℝ) (fun f => by
        change ‖frequencyAction m f‖ ≤ (m.bound : ℝ) * ‖f‖
        exact norm_frequencyAction_le m f)

private theorem hermitian_frequencyAction (m : HermitianSymbol) (f : ComplexL2) :
    hermitianL2CLM (frequencyAction m f) = frequencyAction m (hermitianL2CLM f) := by
  apply Lp.ext
  filter_upwards [hermitianL2_ae (frequencyAction m f),
    ae_neg_of_ae (frequencyAction_ae m f),
    frequencyAction_ae m (hermitianL2CLM f), hermitianL2_ae f]
    with ξ hJ hneg hM hf
  rw [hJ, hneg, hM, hf, conjugateVectorLI_smul, m.reflected_conj]

private theorem conjugate_fourierInv_action (m : HermitianSymbol) (u : SpatialL2) :
    conjugateL2CLM (𝓕⁻ (frequencyAction m (𝓕 (complexifyL2 u)))) =
      𝓕⁻ (frequencyAction m (𝓕 (complexifyL2 u))) := by
  apply (conjugate_eq_iff_hermitian_fourier_eq _).mpr
  rw [fourier_fourierInv_eq, hermitian_frequencyAction, hermitian_fourier_complexify]

private def realAction (m : HermitianSymbol) (u : SpatialL2) : SpatialL2 :=
  realPartL2CLM (𝓕⁻ (frequencyAction m (𝓕 (complexifyL2 u))))

private theorem complexify_realAction (m : HermitianSymbol) (u : SpatialL2) :
    complexifyL2 (realAction m u) =
      𝓕⁻ (frequencyAction m (𝓕 (complexifyL2 u))) :=
  complexify_realPartL2_of_conjugate_eq _ (conjugate_fourierInv_action m u)

private theorem fourier_complexify_realAction (m : HermitianSymbol) (u : SpatialL2) :
    (𝓕 (complexifyL2 (realAction m u)) : ComplexL2) =
      frequencyAction m (𝓕 (complexifyL2 u)) := by
  rw [complexify_realAction, fourier_fourierInv_eq]

private theorem realAction_fourier_ae (m : HermitianSymbol) (u : SpatialL2) :
    (fun ξ : Space => (𝓕 (complexifyL2 (realAction m u)) : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space => m.value ξ • (𝓕 (complexifyL2 u) : ComplexL2) ξ) := by
  rw [fourier_complexify_realAction]
  exact frequencyAction_ae m (𝓕 (complexifyL2 u))

private def complexActionCLM (m : HermitianSymbol) : ComplexL2 →L[ℂ] ComplexL2 :=
  (Lp.fourierTransformₗᵢ Space ComplexVector).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((frequencyActionCLM m).comp
      (Lp.fourierTransformₗᵢ Space ComplexVector).toLinearIsometry.toContinuousLinearMap)

private def realActionCLM (m : HermitianSymbol) : SpatialL2 →L[ℝ] SpatialL2 :=
  realPartL2CLM.comp (((complexActionCLM m).restrictScalars ℝ).comp
    complexifyL2LI.toContinuousLinearMap)

private theorem norm_realAction_le (m : HermitianSymbol) (u : SpatialL2) :
    ‖realAction m u‖ ≤ (m.bound : ℝ) * ‖u‖ := by
  rw [← complexifyL2_norm (realAction m u),
    ← Lp.norm_fourier_eq (complexifyL2 (realAction m u)),
    fourier_complexify_realAction]
  calc
    ‖frequencyAction m (𝓕 (complexifyL2 u))‖ ≤
        (m.bound : ℝ) * ‖(𝓕 (complexifyL2 u) : ComplexL2)‖ :=
      norm_frequencyAction_le m _
    _ = (m.bound : ℝ) * ‖u‖ := by rw [Lp.norm_fourier_eq, complexifyL2_norm]

/-- A sufficient exact first-derivative bound at cutoff radius n+1. -/
def cutoffDerivativeBound (n : ℕ) : ℝ := 2 * Real.pi * cutoffRadius n

theorem cutoffDerivativeBound_pos (n : ℕ) : 0 < cutoffDerivativeBound n := by
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (cutoffRadius_pos n)

private def firstSymbolValue (n : ℕ) (j : Fin 3) (ξ : Space) : ℂ :=
  ((2 * Real.pi * Complex.I) * (inner ℝ ξ (coordinateVector j) : ℂ)) *
    (cutoffValue n ξ : ℂ)

private theorem measurable_firstSymbolValue (n : ℕ) (j : Fin 3) :
    Measurable (firstSymbolValue n j) := by
  have hi : Continuous (fun ξ : Space => inner ℝ ξ (coordinateVector j)) :=
    continuous_id.inner continuous_const
  have hic : Measurable (fun ξ : Space => (inner ℝ ξ (coordinateVector j) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hi.measurable
  have hm : Measurable (fun ξ : Space => (cutoffValue n ξ : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (measurable_cutoffValue n)
  exact (measurable_const.mul hic).mul hm

private theorem firstSymbolValue_reflected_conj (n : ℕ) (j : Fin 3) (ξ : Space) :
    conj (firstSymbolValue n j (-ξ)) = firstSymbolValue n j ξ := by
  simp only [firstSymbolValue, cutoffValue_neg, inner_neg_left, Complex.ofReal_neg,
    map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

private theorem norm_firstSymbolValue_le (n : ℕ) (j : Fin 3) (ξ : Space) :
    ‖firstSymbolValue n j ξ‖ ≤ cutoffDerivativeBound n := by
  by_cases hξ : ‖ξ‖ ≤ cutoffRadius n
  · have hc : |inner ℝ ξ (coordinateVector j)| ≤ ‖ξ‖ := by
      simpa [coordinateVector] using abs_real_inner_le_norm ξ (coordinateVector j)
    calc
      ‖firstSymbolValue n j ξ‖ =
          (2 * Real.pi) * |inner ℝ ξ (coordinateVector j)| := by
        simp [firstSymbolValue, cutoffValue, hξ, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      _ ≤ (2 * Real.pi) * cutoffRadius n :=
        mul_le_mul_of_nonneg_left (hc.trans hξ) (by positivity)
      _ = cutoffDerivativeBound n := rfl
  · simpa [firstSymbolValue, cutoffValue, hξ] using (cutoffDerivativeBound_pos n).le

private def firstSymbol (n : ℕ) (j : Fin 3) : HermitianSymbol where
  value := firstSymbolValue n j
  measurable := measurable_firstSymbolValue n j
  reflected_conj := firstSymbolValue_reflected_conj n j
  bound := ⟨cutoffDerivativeBound n, (cutoffDerivativeBound_pos n).le⟩
  norm_le := norm_firstSymbolValue_le n j

/-- Actual real L2 first derivatives are constructed by the imaginary-odd
bounded Fourier symbols, not supplied as regularity witnesses. -/
def cutoffDerivative (n : ℕ) (j : Fin 3) : SpatialL2 →L[ℝ] SpatialL2 :=
  realActionCLM (firstSymbol n j)

/-- The constructed field has exactly the weak derivative symbol of J_n u. -/
theorem cutoffDerivative_fourier_ae (n : ℕ) (j : Fin 3) (u : SpatialL2) :
    (fun ξ : Space => (𝓕 (complexifyL2 (cutoffDerivative n j u)) : ComplexL2) ξ)
      =ᵐ[volume] (fun ξ : Space =>
        ((2 * Real.pi * Complex.I) * (inner ℝ ξ (coordinateVector j) : ℂ)) •
          (𝓕 (complexifyL2 (sharpCutoff n u)) : ComplexL2) ξ) := by
  have hd := realAction_fourier_ae (firstSymbol n j) u
  change (fun ξ : Space =>
    (𝓕 (complexifyL2 (cutoffDerivative n j u)) : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space => firstSymbolValue n j ξ •
        (𝓕 (complexifyL2 u) : ComplexL2) ξ) at hd
  filter_upwards [hd, sharpCutoff_fourier_ae n u] with ξ hD hJ
  rw [hD, hJ]
  simp only [firstSymbolValue, smul_smul]

theorem norm_cutoffDerivative_le (n : ℕ) (j : Fin 3) (u : SpatialL2) :
    ‖cutoffDerivative n j u‖ ≤ cutoffDerivativeBound n * ‖u‖ := by
  change ‖realAction (firstSymbol n j) u‖ ≤ cutoffDerivativeBound n * ‖u‖
  exact norm_realAction_le (firstSymbol n j) u

/-- The derivative remains in the same actual frequency ball. -/
theorem sharpCutoff_cutoffDerivative (n : ℕ) (j : Fin 3) (u : SpatialL2) :
    sharpCutoff n (cutoffDerivative n j u) = cutoffDerivative n j u := by
  apply complexifyL2LI.injective
  apply (Lp.fourierTransformₗᵢ Space ComplexVector).injective
  change (𝓕 (complexifyL2 (sharpCutoff n (cutoffDerivative n j u))) : ComplexL2) =
    𝓕 (complexifyL2 (cutoffDerivative n j u))
  apply Lp.ext
  filter_upwards [sharpCutoff_fourier_ae n (cutoffDerivative n j u),
    cutoffDerivative_fourier_ae n j u, sharpCutoff_fourier_ae n u]
    with ξ ho hD hJ
  simp only [ho, hD, hJ]
  by_cases hξ : ‖ξ‖ ≤ cutoffRadius n <;> simp [cutoffValue, hξ]

/-- Every actual L2 input acquires its three native compact-test weak
derivatives after the sharp cutoff. -/
theorem spatialWeakGradient_sharpCutoff_constructed (n : ℕ) (u : SpatialL2) :
    SpatialWeakGradient (sharpCutoff n u) (fun j => cutoffDerivative n j u) := by
  apply (H1Fourier.spatialWeakGradient_iff_fourier_ae _ _).mpr
  exact ae_all_iff.mpr (fun j => cutoffDerivative_fourier_ae n j u)

/-- For already supplied native derivatives, the construction agrees with
cutting off those derivatives. This is a conclusion by derivative uniqueness. -/
theorem cutoffDerivative_eq_sharpCutoff_of_weakGradient
    (n : ℕ) {u : SpatialL2} {G : Fin 3 → SpatialL2}
    (hG : SpatialWeakGradient u G) (j : Fin 3) :
    cutoffDerivative n j u = sharpCutoff n (G j) := by
  exact congrFun (spatialWeakGradient_unique
    (spatialWeakGradient_sharpCutoff_constructed n u)
    (spatialWeakGradient_sharpCutoff n hG)) j

theorem cutoffDerivative_sharpCutoff (n : ℕ) (j : Fin 3) (u : SpatialL2) :
    cutoffDerivative n j (sharpCutoff n u) = cutoffDerivative n j u := by
  have h := spatialWeakGradient_sharpCutoff_constructed n (sharpCutoff n u)
  rw [sharpCutoff_idempotent] at h
  exact congrFun (spatialWeakGradient_unique h
    (spatialWeakGradient_sharpCutoff_constructed n u)) j

/-- Applying the bounded first-derivative construction twice supplies every
actual ordered weak Hessian entry. -/
theorem spatialWeakHessian_sharpCutoff_constructed (n : ℕ) (u : SpatialL2) :
    SpatialWeakHessian (fun j => cutoffDerivative n j u)
      (fun j k => cutoffDerivative n k (cutoffDerivative n j u)) := by
  intro j
  have h := spatialWeakGradient_sharpCutoff_constructed n (cutoffDerivative n j u)
  rw [sharpCutoff_cutoffDerivative] at h
  exact h

/-- Actual physical H2 output for every real L2 input. -/
def sharpCutoffH2 (n : ℕ) (u : SpatialL2) : PhysicalH2 :=
  physicalH2OfWeakDerivatives (sharpCutoff n u)
    (fun j => cutoffDerivative n j u)
    (fun j k => cutoffDerivative n k (cutoffDerivative n j u))
    (spatialWeakGradient_sharpCutoff_constructed n u)
    (spatialWeakHessian_sharpCutoff_constructed n u)

@[simp] theorem sharpCutoffH2_velocity (n : ℕ) (u : SpatialL2) :
    physicalH2Velocity (sharpCutoffH2 n u) = sharpCutoff n u := rfl

@[simp] theorem sharpCutoffH2_gradient (n : ℕ) (u : SpatialL2) (j : Fin 3) :
    physicalH2Gradient j (sharpCutoffH2 n u) = cutoffDerivative n j u := rfl

@[simp] theorem sharpCutoffH2_hessian (n : ℕ) (u : SpatialL2) (j k : Fin 3) :
    physicalH2Hessian j k (sharpCutoffH2 n u) =
      cutoffDerivative n k (cutoffDerivative n j u) := rfl

/-- A nonsharp component-count bound, sufficient for a fixed-cutoff H2 lift. -/
theorem sharpCutoffH2_norm_sq_le (n : ℕ) (u : SpatialL2) :
    ‖sharpCutoffH2 n u‖ ^ 2 ≤
      (1 + 3 * (cutoffDerivativeBound n) ^ 2 +
        9 * (cutoffDerivativeBound n) ^ 4) * ‖u‖ ^ 2 := by
  let L := cutoffDerivativeBound n
  have hL : 0 ≤ L := (cutoffDerivativeBound_pos n).le
  have hv : ‖sharpCutoff n u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sharpCutoff_le n u) 2
  have hG (j : Fin 3) : ‖cutoffDerivative n j u‖ ^ 2 ≤ L ^ 2 * ‖u‖ ^ 2 := by
    simpa only [mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _) (norm_cutoffDerivative_le n j u) 2
  have hH (j k : Fin 3) :
      ‖cutoffDerivative n k (cutoffDerivative n j u)‖ ^ 2 ≤ L ^ 4 * ‖u‖ ^ 2 := by
    have hnorm : ‖cutoffDerivative n k (cutoffDerivative n j u)‖ ≤ L ^ 2 * ‖u‖ := by
      calc
        _ ≤ L * ‖cutoffDerivative n j u‖ := norm_cutoffDerivative_le n k _
        _ ≤ L * (L * ‖u‖) :=
          mul_le_mul_of_nonneg_left (norm_cutoffDerivative_le n j u) hL
        _ = L ^ 2 * ‖u‖ := by ring
    calc
      _ ≤ (L ^ 2 * ‖u‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = L ^ 4 * ‖u‖ ^ 2 := by ring
  rw [physicalH2_norm_sq]
  simp only [sharpCutoffH2_velocity, sharpCutoffH2_gradient, sharpCutoffH2_hessian]
  calc
    _ ≤ ‖u‖ ^ 2 + (∑ _j : Fin 3, L ^ 2 * ‖u‖ ^ 2) +
        ∑ _j : Fin 3, ∑ _k : Fin 3, L ^ 4 * ‖u‖ ^ 2 :=
      add_le_add (add_le_add hv (Finset.sum_le_sum fun j _ => hG j))
        (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hH j k)
    _ = (1 + 3 * (cutoffDerivativeBound n) ^ 2 +
          9 * (cutoffDerivativeBound n) ^ 4) * ‖u‖ ^ 2 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
      dsimp [L]
      ring

def sharpCutoffH2Bound (n : ℕ) : ℝ :=
  Real.sqrt (1 + 3 * (cutoffDerivativeBound n) ^ 2 +
    9 * (cutoffDerivativeBound n) ^ 4)

theorem norm_sharpCutoffH2_le (n : ℕ) (u : SpatialL2) :
    ‖sharpCutoffH2 n u‖ ≤ sharpCutoffH2Bound n * ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  change ‖sharpCutoffH2 n u‖ ^ 2 ≤
    (Real.sqrt (1 + 3 * (cutoffDerivativeBound n) ^ 2 +
      9 * (cutoffDerivativeBound n) ^ 4) * ‖u‖) ^ 2
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact sharpCutoffH2_norm_sq_le n u

/-- The actual H2 construction is a bounded real-linear operator on all L2. -/
def sharpCutoffH2CLM (n : ℕ) : SpatialL2 →L[ℝ] PhysicalH2 :=
  ({ toFun := sharpCutoffH2 n
     map_add' := by
       intro u v
       apply physicalH2Velocity_injective
       simp only [sharpCutoffH2_velocity, map_add]
     map_smul' := by
       intro r u
       apply physicalH2Velocity_injective
       simp only [sharpCutoffH2_velocity, map_smul, RingHom.id_apply] } :
    SpatialL2 →ₗ[ℝ] PhysicalH2).mkContinuous (sharpCutoffH2Bound n) (by
      intro u
      change ‖sharpCutoffH2 n u‖ ≤ sharpCutoffH2Bound n * ‖u‖
      exact norm_sharpCutoffH2_le n u)

@[simp] theorem sharpCutoffH2CLM_apply (n : ℕ) (u : SpatialL2) :
    sharpCutoffH2CLM n u = sharpCutoffH2 n u := rfl

/-- The new L2-to-H2 construction agrees with the existing H1 cutoff lift. -/
theorem sharpCutoffH2_toH1 (n : ℕ) (u : PhysicalH1) :
    physicalH2ToH1 (sharpCutoffH2 n (physicalH1Velocity u)) =
      physicalH1SharpCutoff n u := by
  apply physicalH1Velocity_injective
  simp only [physicalH2ToH1_velocity, sharpCutoffH2_velocity,
    physicalH1SharpCutoff_velocity]

/-- Any already bandlimited physical H2 field is recovered without changing
its actual weak derivatives. -/
theorem sharpCutoffH2_eq_of_fixed (n : ℕ) (u : PhysicalH2)
    (hu : sharpCutoff n (physicalH2Velocity u) = physicalH2Velocity u) :
    sharpCutoffH2 n (physicalH2Velocity u) = u := by
  apply physicalH2Velocity_injective
  simpa only [sharpCutoffH2_velocity] using hu

end MethbokeAddon.R3Ehrenfest.Bandlimited
