import MethbokeAddon.QuasiFeffermanA.RealFourier
import MethbokeAddon.QuasiFeffermanA.H1FourierReverse
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Actual bounded real even Fourier multipliers

A measurable bounded even real scalar symbol acts on actual complex L2
representatives. Its proved commutation with conjugate-reflection constructs
an actual real L2 Fourier operator. Native Fourier injectivity determines the
operator uniquely, and the accepted reverse derivative bridge proves weak
gradient commutation. No physical reality or derivative conclusion is an
input premise.

The scalar convention is `(m.value ξ : ℂ) • f ξ`. This module is reusable by
the heat and elliptic reconstruction developments. Their special symbol and
evolution identities remain separate proofs.

Prepared source requires matching cached external compiler and full named
type/axiom evidence. No local Lean, Lake or kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform NNReal

namespace MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open RealFourier

/-- A literal scalar symbol and its elementary measurable/even/bounded data. -/
structure RealEvenSymbol where
  value : Space → ℝ
  measurable : Measurable value
  even : ∀ ξ : Space, value (-ξ) = value ξ
  bound : ℝ≥0
  norm_le : ∀ ξ : Space, ‖value ξ‖ ≤ (bound : ℝ)

/-- The actual representative belongs to L2 by its finite pointwise bound. -/
theorem memLp_symbol_smul (m : RealEvenSymbol) (f : ComplexL2) :
    MemLp (fun ξ : Space => (m.value ξ : ℂ) • f ξ) 2 volume := by
  have hm : Measurable (fun ξ : Space => (m.value ξ : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp m.measurable
  apply (Lp.memLp f).of_le_mul
    (hm.aestronglyMeasurable.smul (Lp.aestronglyMeasurable f))
  filter_upwards with ξ
  rw [norm_smul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (m.norm_le ξ) (norm_nonneg _)

def frequencyMultiplier (m : RealEvenSymbol) (f : ComplexL2) : ComplexL2 :=
  (memLp_symbol_smul m f).toLp (fun ξ : Space => (m.value ξ : ℂ) • f ξ)

theorem frequencyMultiplier_ae (m : RealEvenSymbol) (f : ComplexL2) :
    (fun ξ : Space => frequencyMultiplier m f ξ) =ᵐ[volume]
      (fun ξ : Space => (m.value ξ : ℂ) • f ξ) := MemLp.coeFn_toLp _

theorem norm_frequencyMultiplier_le (m : RealEvenSymbol) (f : ComplexL2) :
    ‖frequencyMultiplier m f‖ ≤ (m.bound : ℝ) * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [frequencyMultiplier_ae m f] with ξ hξ
  rw [hξ, norm_smul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (m.norm_le ξ) (norm_nonneg _)

theorem frequencyMultiplier_add (m : RealEvenSymbol) (f g : ComplexL2) :
    frequencyMultiplier m (f + g) = frequencyMultiplier m f + frequencyMultiplier m g := by
  apply Lp.ext
  filter_upwards [frequencyMultiplier_ae m (f + g), frequencyMultiplier_ae m f,
    frequencyMultiplier_ae m g, Lp.coeFn_add f g,
    Lp.coeFn_add (frequencyMultiplier m f) (frequencyMultiplier m g)]
    with ξ hsum hf hg hadd htarget
  rw [hsum, htarget, Pi.add_apply, hadd, Pi.add_apply, hf, hg, smul_add]

theorem frequencyMultiplier_smul (m : RealEvenSymbol) (c : ℂ) (f : ComplexL2) :
    frequencyMultiplier m (c • f) = c • frequencyMultiplier m f := by
  apply Lp.ext
  filter_upwards [frequencyMultiplier_ae m (c • f), frequencyMultiplier_ae m f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (frequencyMultiplier m f)]
    with ξ hscaled hf hsource htarget
  rw [hscaled, htarget, Pi.smul_apply, hsource, Pi.smul_apply, hf]
  exact smul_comm _ _ _

@[simp] theorem frequencyMultiplier_zero (m : RealEvenSymbol) :
    frequencyMultiplier m 0 = 0 := by
  have h := frequencyMultiplier_smul m (0 : ℂ) (0 : ComplexL2)
  simpa only [zero_smul] using h

def frequencyMultiplierCLM (m : RealEvenSymbol) : ComplexL2 →L[ℂ] ComplexL2 :=
  ({ toFun := frequencyMultiplier m
     map_add' := frequencyMultiplier_add m
     map_smul' := frequencyMultiplier_smul m } : ComplexL2 →ₗ[ℂ] ComplexL2).mkContinuous
      (m.bound : ℝ) (fun f => by
        change ‖frequencyMultiplier m f‖ ≤ (m.bound : ℝ) * ‖f‖
        exact norm_frequencyMultiplier_le m f)

@[simp] theorem frequencyMultiplierCLM_apply (m : RealEvenSymbol) (f : ComplexL2) :
    frequencyMultiplierCLM m f = frequencyMultiplier m f := rfl

/-- Evenness and reality prove exact commutation with the Hermitian involution. -/
theorem hermitian_frequencyMultiplier (m : RealEvenSymbol) (f : ComplexL2) :
    hermitianL2CLM (frequencyMultiplier m f) = frequencyMultiplier m (hermitianL2CLM f) := by
  apply Lp.ext
  filter_upwards [hermitianL2_ae (frequencyMultiplier m f),
    ae_neg_of_ae (frequencyMultiplier_ae m f),
    frequencyMultiplier_ae m (hermitianL2CLM f), hermitianL2_ae f]
    with ξ hJ hneg hM hf
  rw [hJ, hneg, hM, hf, conjugateVectorLI_smul, m.even, Complex.conj_ofReal]

private theorem conjugate_fourierInv_multiplier (m : RealEvenSymbol) (u : SpatialL2) :
    conjugateL2CLM (𝓕⁻ (frequencyMultiplier m (𝓕 (complexifyL2 u)))) =
      𝓕⁻ (frequencyMultiplier m (𝓕 (complexifyL2 u))) := by
  apply (conjugate_eq_iff_hermitian_fourier_eq _).mpr
  rw [fourier_fourierInv_eq, hermitian_frequencyMultiplier, hermitian_fourier_complexify]

/-- Actual real L2 action is constructed using the proved real Fourier range. -/
def realFourierMultiplier (m : RealEvenSymbol) (u : SpatialL2) : SpatialL2 :=
  realPartL2CLM (𝓕⁻ (frequencyMultiplier m (𝓕 (complexifyL2 u))))

theorem complexify_realFourierMultiplier (m : RealEvenSymbol) (u : SpatialL2) :
    complexifyL2 (realFourierMultiplier m u) =
      𝓕⁻ (frequencyMultiplier m (𝓕 (complexifyL2 u))) :=
  complexify_realPartL2_of_conjugate_eq _ (conjugate_fourierInv_multiplier m u)

theorem fourier_complexify_realFourierMultiplier (m : RealEvenSymbol) (u : SpatialL2) :
    (𝓕 (complexifyL2 (realFourierMultiplier m u)) : ComplexL2) =
      frequencyMultiplier m (𝓕 (complexifyL2 u)) := by
  rw [complexify_realFourierMultiplier, fourier_fourierInv_eq]

theorem fourier_complexify_realFourierMultiplier_ae (m : RealEvenSymbol) (u : SpatialL2) :
    (fun ξ : Space => (𝓕 (complexifyL2 (realFourierMultiplier m u)) : ComplexL2) ξ)
      =ᵐ[volume] (fun ξ : Space =>
        (m.value ξ : ℂ) • (𝓕 (complexifyL2 u) : ComplexL2) ξ) := by
  rw [fourier_complexify_realFourierMultiplier]
  exact frequencyMultiplier_ae m (𝓕 (complexifyL2 u))

private def complexFourierMultiplierCLM (m : RealEvenSymbol) : ComplexL2 →L[ℂ] ComplexL2 :=
  (Lp.fourierTransformₗᵢ Space ComplexVector).symm.toContinuousLinearMap.comp
    ((frequencyMultiplierCLM m).comp
      (Lp.fourierTransformₗᵢ Space ComplexVector).toContinuousLinearMap)

def realFourierMultiplierCLM (m : RealEvenSymbol) : SpatialL2 →L[ℝ] SpatialL2 :=
  realPartL2CLM.comp (((complexFourierMultiplierCLM m).restrictScalars ℝ).comp
    complexifyL2LI.toContinuousLinearMap)

@[simp] theorem realFourierMultiplierCLM_apply (m : RealEvenSymbol) (u : SpatialL2) :
    realFourierMultiplierCLM m u = realFourierMultiplier m u := rfl

theorem realFourierMultiplier_add (m : RealEvenSymbol) (u v : SpatialL2) :
    realFourierMultiplier m (u + v) = realFourierMultiplier m u + realFourierMultiplier m v :=
  (realFourierMultiplierCLM m).map_add u v

theorem realFourierMultiplier_smul (m : RealEvenSymbol) (r : ℝ) (u : SpatialL2) :
    realFourierMultiplier m (r • u) = r • realFourierMultiplier m u :=
  (realFourierMultiplierCLM m).map_smul r u

@[simp] theorem realFourierMultiplier_zero (m : RealEvenSymbol) :
    realFourierMultiplier m 0 = 0 := (realFourierMultiplierCLM m).map_zero

theorem norm_realFourierMultiplier_le (m : RealEvenSymbol) (u : SpatialL2) :
    ‖realFourierMultiplier m u‖ ≤ (m.bound : ℝ) * ‖u‖ := by
  rw [← complexifyL2_norm (realFourierMultiplier m u),
    ← Lp.norm_fourier_eq (complexifyL2 (realFourierMultiplier m u)),
    fourier_complexify_realFourierMultiplier]
  calc
    ‖frequencyMultiplier m (𝓕 (complexifyL2 u))‖ ≤
        (m.bound : ℝ) * ‖(𝓕 (complexifyL2 u) : ComplexL2)‖ :=
      norm_frequencyMultiplier_le m _
    _ = (m.bound : ℝ) * ‖u‖ := by rw [Lp.norm_fourier_eq, complexifyL2_norm]

/-- Actual real L2 output is uniquely determined by its literal Fourier symbol. -/
theorem realFourierMultiplier_eq_of_fourier_ae
    (m : RealEvenSymbol) (u v : SpatialL2)
    (h : (fun ξ : Space => (𝓕 (complexifyL2 v) : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space => (m.value ξ : ℂ) • (𝓕 (complexifyL2 u) : ComplexL2) ξ)) :
    v = realFourierMultiplier m u := by
  apply complexifyL2LI.injective
  apply (Lp.fourierTransformₗᵢ Space ComplexVector).injective
  apply Lp.ext
  filter_upwards [h, fourier_complexify_realFourierMultiplier_ae m u] with ξ hv hQ
  exact hv.trans hQ.symm

/-- Scalar multiplication commutes on actual supplied L2 representatives. -/
theorem frequencyMultiplier_multiplier_ae (m : RealEvenSymbol)
    (f g : ComplexL2) (a : Space → ℂ)
    (h : (fun ξ : Space => g ξ) =ᵐ[volume] (fun ξ : Space => a ξ • f ξ)) :
    (fun ξ : Space => frequencyMultiplier m g ξ) =ᵐ[volume]
      (fun ξ : Space => a ξ • frequencyMultiplier m f ξ) := by
  filter_upwards [frequencyMultiplier_ae m g, frequencyMultiplier_ae m f, h]
    with ξ hg hf hgf
  rw [hg, hf, hgf]
  exact smul_comm _ _ _

/-- The actual projected supplied first derivatives satisfy the native weak
gradient condition, with no differentiability requirement on the symbol. -/
theorem spatialWeakGradient_realFourierMultiplier (m : RealEvenSymbol)
    {v : SpatialL2} {G : Fin 3 → SpatialL2} (h : SpatialWeakGradient v G) :
    SpatialWeakGradient (realFourierMultiplier m v)
      (fun j => realFourierMultiplier m (G j)) := by
  apply (H1Fourier.spatialWeakGradient_iff_fourier_ae _ _).mpr
  have hfreq := (H1Fourier.spatialWeakGradient_iff_fourier_ae v G).mp h
  apply ae_all_iff.mpr
  intro j
  have hp := frequencyMultiplier_multiplier_ae m
    (𝓕 (complexifyL2 v) : ComplexL2) (𝓕 (complexifyL2 (G j)) : ComplexL2)
    (fun ξ : Space => (2 * Real.pi * Complex.I) *
      (inner ℝ ξ (coordinateVector j) : ℂ)) (ae_all_iff.mp hfreq j)
  filter_upwards [hp] with ξ hξ
  simpa only [fourier_complexify_realFourierMultiplier] using hξ

end MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers
