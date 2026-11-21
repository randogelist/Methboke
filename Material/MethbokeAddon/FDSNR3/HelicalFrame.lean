import MethbokeAddon.FDSNR3.Helical
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Fixed-frame scalar interpretation of intrinsic helical powers

An ordinary orthonormal basis, its normalized longitudinal vector and
actual curl eigenvector equations imply the projector coefficient formula.
The squared scalar Fourier amplitude equals the intrinsic helical power.
-/

set_option autoImplicit false

open SingularClosure
open scoped BigOperators ComplexConjugate

namespace MethbokeAddon.FDSNR3

noncomputable section

/-- In any fixed orthonormal helical frame, the intrinsic helical projector is
the rank-one projector onto the corresponding actual curl eigenvector. -/
theorem helicalSymbol_eq_inner_smul_of_orthonormal_curl_frame
    {ξ : Vec} (hξ : ξ ≠ 0) (b : OrthonormalBasis (Fin 3) ℂ CVec)
    (hcurl : ∀ τ : Fin 2,
      Complex.I • complexCross ξ (b τ.castSucc) =
        ((helicitySign τ : ℂ) * (‖ξ‖ : ℂ)) • b τ.castSucc)
    (hlong : b 2 = (‖ξ‖ : ℂ)⁻¹ • complexify ξ)
    (σ : Fin 2) (z : CVec) :
    helicalSymbol σ ξ z =
      (inner ℂ (b σ.castSucc) z) • b σ.castSucc := by
  have hn : (‖ξ‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hξ)
  have hn2 : ((‖ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ))
  have heigen : ∀ τ : Fin 2,
      helicityOperator ξ (b τ.castSucc) =
        (helicitySign τ : ℂ) • b τ.castSucc := by
    intro τ
    have hs : (‖ξ‖ : ℂ)⁻¹ * ((helicitySign τ : ℂ) * (‖ξ‖ : ℂ)) =
        (helicitySign τ : ℂ) := by
      calc
        (‖ξ‖ : ℂ)⁻¹ * ((helicitySign τ : ℂ) * (‖ξ‖ : ℂ)) =
            (helicitySign τ : ℂ) * ((‖ξ‖ : ℂ)⁻¹ * (‖ξ‖ : ℂ)) := by ring
        _ = (helicitySign τ : ℂ) := by rw [inv_mul_cancel₀ hn, mul_one]
    calc
      helicityOperator ξ (b τ.castSucc) =
          (‖ξ‖ : ℂ)⁻¹ • (Complex.I • complexCross ξ (b τ.castSucc)) := by
        simp only [helicityOperator, div_eq_mul_inv, smul_smul]
        congr 1
        exact mul_comm _ _
      _ = (‖ξ‖ : ℂ)⁻¹ •
          (((helicitySign τ : ℂ) * (‖ξ‖ : ℂ)) • b τ.castSucc) :=
        congrArg (fun w : CVec => (‖ξ‖ : ℂ)⁻¹ • w) (hcurl τ)
      _ = (helicitySign τ : ℂ) • b τ.castSucc := by rw [smul_smul, hs]
  have htrans : ∀ τ : Fin 2,
      transverseSymbol ξ (b τ.castSucc) = b τ.castSucc := by
    intro τ
    calc
      transverseSymbol ξ (b τ.castSucc) =
          helicityOperator ξ (helicityOperator ξ (b τ.castSucc)) :=
        (helicityOperator_sq hξ (b τ.castSucc)).symm
      _ = (helicitySign τ : ℂ) • ((helicitySign τ : ℂ) • b τ.castSucc) := by
        rw [heigen, helicityOperator_smul, heigen]
      _ = b τ.castSucc := by
        rw [smul_smul, helicitySign_mul_self, one_smul]
  have hproject : ∀ τ : Fin 2,
      helicalSymbol σ ξ (b τ.castSucc) =
        (if σ = τ then (1 : ℂ) else 0) • b τ.castSucc := by
    intro τ
    have hsum : b τ.castSucc +
        ((helicitySign σ : ℂ) * (helicitySign τ : ℂ)) • b τ.castSucc =
        (1 + (helicitySign σ : ℂ) * (helicitySign τ : ℂ)) • b τ.castSucc := by
      rw [add_smul, one_smul]
    rw [helicalSymbol_eq, htrans, heigen, smul_smul, hsum, smul_smul]
    congr 1
    fin_cases σ <;> fin_cases τ <;> norm_num [helicitySign]
  have htrans_long : transverseSymbol ξ (complexify ξ) = 0 := by
    rw [transverseSymbol_eq, frequencyDot_complexify, div_self hn2, one_smul, sub_self]
  have hproject_long : helicalSymbol σ ξ (b 2) = 0 := by
    rw [hlong, helicalSymbol_smul]
    simp only [helicalSymbol, htrans_long, complexCross_complexify, smul_zero, add_zero]
  have h0 : helicalSymbol σ ξ (b 0) =
      (if σ = 0 then (1 : ℂ) else 0) • b 0 := hproject 0
  have h1 : helicalSymbol σ ξ (b 1) =
      (if σ = 1 then (1 : ℂ) else 0) • b 1 := hproject 1
  have hsum := congrArg (helicalSymbol σ ξ) (b.sum_repr' z)
  simp only [Fin.sum_univ_three, helicalSymbol_add, helicalSymbol_smul,
    h0, h1, hproject_long, smul_zero, add_zero] at hsum
  fin_cases σ <;> simpa using hsum.symm

/-- The intrinsic modal power is the squared magnitude of the scalar
coefficient in any fixed orthonormal frame of actual helical eigenvectors. -/
theorem norm_helicalSymbol_sq_eq_inner_sq_of_orthonormal_curl_frame
    {ξ : Vec} (hξ : ξ ≠ 0) (b : OrthonormalBasis (Fin 3) ℂ CVec)
    (hcurl : ∀ τ : Fin 2,
      Complex.I • complexCross ξ (b τ.castSucc) =
        ((helicitySign τ : ℂ) * (‖ξ‖ : ℂ)) • b τ.castSucc)
    (hlong : b 2 = (‖ξ‖ : ℂ)⁻¹ • complexify ξ)
    (σ : Fin 2) (z : CVec) :
    ‖helicalSymbol σ ξ z‖ ^ 2 =
      ‖inner ℂ (b σ.castSucc) z‖ ^ 2 := by
  rw [helicalSymbol_eq_inner_smul_of_orthonormal_curl_frame hξ b hcurl hlong,
    norm_smul, b.norm_eq_one, mul_one]

/-- The actual Fourier helical power density equals the squared scalar
helical Fourier amplitude in every fixed orthonormal curl eigenframe. -/
theorem helicalPower_eq_inner_sq_of_orthonormal_curl_frame
    {ξ : Vec} (hξ : ξ ≠ 0) (b : OrthonormalBasis (Fin 3) ℂ CVec)
    (hcurl : ∀ τ : Fin 2,
      Complex.I • complexCross ξ (b τ.castSucc) =
        ((helicitySign τ : ℂ) * (‖ξ‖ : ℂ)) • b τ.castSucc)
    (hlong : b 2 = (‖ξ‖ : ℂ)⁻¹ • complexify ξ)
    (σ : Fin 2) (v : Field) :
    helicalPower σ v ξ =
      ‖inner ℂ (b σ.castSucc) (fourierVelocity v ξ)‖ ^ 2 :=
  norm_helicalSymbol_sq_eq_inner_sq_of_orthonormal_curl_frame
    hξ b hcurl hlong σ (fourierVelocity v ξ)

end

end MethbokeAddon.FDSNR3
