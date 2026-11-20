import MethbokeAddon.QuasiFeffermanA.FourierMultipliers
import Mathlib.Analysis.Complex.Norm

/-!
# Whole-space spectral realization from actual derivative witnesses

The supplied Schwartz-distribution derivative identities determine the Fourier
multiplier representatives almost everywhere. Complex scalar norm identities
and the three-coordinate Euclidean norm identity give the two Fourier norm
densities. The existing Plancherel assembly then supplies integrability and all
three energy identities, with every native `2 * pi` factor retained.

This is prepared source. Matching external compiler, exact-type and transitive
axiom evidence are required. No local Lean, Lake or kernel execution was used.
The conclusion inhabits the spectral endpoint; it asserts no NSE existence,
temporal regularity, Agmon estimate or physical weak-gradient construction.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform

namespace MethbokeAddon.QuasiFeffermanA

open QFA.Endpoints.Agmon
open QFA.LC001SpectralReduction
open MethbokeAddon.QuasiFeffermanA.FourierMultipliers

noncomputable section

private theorem norm_sq_real_I_product_smul
    (a b : ℝ) (z : ComplexVector) :
    ‖(((a : ℂ) * Complex.I) * (b : ℂ)) • z‖ ^ 2 =
      a ^ 2 * b ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_smul, mul_pow, Complex.sq_norm]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_I, one_mul, pow_two, mul_assoc]

private theorem norm_sq_real_product_smul
    (a b : ℝ) (z : ComplexVector) :
    ‖((a : ℂ) * (b : ℂ)) • z‖ ^ 2 =
      a ^ 2 * b ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_smul, mul_pow, Complex.sq_norm]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal, pow_two, mul_assoc]

private theorem gradient_multiplier_norm_sq
    (b : ℝ) (z : ComplexVector) :
    ‖((2 * Real.pi * Complex.I) * (b : ℂ)) • z‖ ^ 2 =
      (2 * Real.pi) ^ 2 * b ^ 2 * ‖z‖ ^ 2 := by
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
    norm_sq_real_I_product_smul (2 * Real.pi) b z

private theorem laplacian_multiplier_norm_sq
    (r : ℝ) (z : ComplexVector) :
    ‖((-((2 * Real.pi) ^ 2) : ℂ) * (r ^ 2 : ℂ)) • z‖ ^ 2 =
      (2 * Real.pi) ^ 4 * r ^ 4 * ‖z‖ ^ 2 := by
  rw [norm_smul, mul_pow, Complex.sq_norm]
  simp only [Complex.normSq_mul, Complex.normSq_neg, map_pow,
    Complex.normSq_ofNat, Complex.normSq_ofReal]
  ring

/-- The actual distributional first-derivative and Laplacian witnesses imply
both almost-everywhere Fourier norm-density identities. No norm-density,
integrability or spectral-realization hypothesis is added. -/
theorem fourierNormAEWitnesses_of_schwartzDerivativeWitnesses
    {v : ComplexL2} {G : Fin 3 → ComplexL2} {L : ComplexL2}
    (h : SchwartzDerivativeWitnesses v G L) :
    FourierNormAEWitnesses v G L := by
  constructor
  · have hgradient : ∀ᵐ k : Space ∂volume, ∀ j : Fin 3,
        (𝓕 (G j) : ComplexL2) k =
          ((2 * Real.pi * Complex.I) *
            (inner ℝ k (EuclideanSpace.basisFun (Fin 3) ℝ j) : ℂ)) •
              (𝓕 v : ComplexL2) k := by
      exact ae_all_iff.mpr (fun j : Fin 3 => gradient_fourier_ae h j)
    filter_upwards [hgradient] with k hk
    change (∑ j : Fin 3, ‖(𝓕 (G j) : ComplexL2) k‖ ^ 2) =
      (2 * Real.pi) ^ 2 * ‖k‖ ^ 2 * ‖(𝓕 v : ComplexL2) k‖ ^ 2
    calc
      (∑ j : Fin 3, ‖(𝓕 (G j) : ComplexL2) k‖ ^ 2) =
          ∑ j : Fin 3,
            (2 * Real.pi) ^ 2 * (k j) ^ 2 * ‖(𝓕 v : ComplexL2) k‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hk j, EuclideanSpace.inner_basisFun_real]
        exact gradient_multiplier_norm_sq (k j) ((𝓕 v : ComplexL2) k)
      _ = (2 * Real.pi) ^ 2 * (∑ j : Fin 3, (k j) ^ 2) *
          ‖(𝓕 v : ComplexL2) k‖ ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = (2 * Real.pi) ^ 2 * ‖k‖ ^ 2 * ‖(𝓕 v : ComplexL2) k‖ ^ 2 := by
        rw [← EuclideanSpace.real_norm_sq_eq k]
  · filter_upwards [laplacian_fourier_ae h] with k hk
    change ‖(𝓕 L : ComplexL2) k‖ ^ 2 =
      (2 * Real.pi) ^ 4 * ‖k‖ ^ 4 * ‖(𝓕 v : ComplexL2) k‖ ^ 2
    rw [hk]
    exact laplacian_multiplier_norm_sq ‖k‖ ((𝓕 v : ComplexL2) k)

/-- Plancherel converts the proved Fourier norm identities into all six
native spectral fields, including genuine weighted integrability. -/
theorem nativeSpectralRealization_of_schwartzDerivativeWitnesses
    {v : ComplexL2} {G : Fin 3 → ComplexL2} {L : ComplexL2}
    (h : SchwartzDerivativeWitnesses v G L) :
    NativeSpectralRealization v G L := by
  exact nativeSpectralRealization_of_fourierNormAE
    (fourierNormAEWitnesses_of_schwartzDerivativeWitnesses h)

/-- Inhabit the existing whole-space spectral endpoint directly from its
stated distributional derivative witnesses. -/
theorem wholeSpaceSpectralEndpoint : WholeSpaceSpectralEndpoint := by
  intro v G L h
  exact nativeSpectralRealization_of_schwartzDerivativeWitnesses h

end

end MethbokeAddon.QuasiFeffermanA
