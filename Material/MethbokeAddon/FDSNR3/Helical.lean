import MethbokeAddon.FDSNR3.Contracts
import MethbokeAddon.FDSNR3.Phase
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Intrinsic whole-space transverse and helical projection algebra

Every operator below is the literal coordinate formula in Contracts.
No eigenframe, projector law, or spectral conclusion is assumed.
The pointwise algebra applies before Fourier reconstruction.
-/

set_option autoImplicit false

open SingularClosure
open scoped BigOperators ComplexConjugate

namespace MethbokeAddon.FDSNR3

noncomputable section

/-- Bilinear frequency pairing with a real frequency and complex vector. -/
def frequencyDot (ξ : Vec) (z : CVec) : ℂ :=
  ∑ i : Fin 3, (ξ i : ℂ) * z i

theorem frequencyDot_add (ξ : Vec) (z w : CVec) :
    frequencyDot ξ (z + w) = frequencyDot ξ z + frequencyDot ξ w := by
  change (∑ i : Fin 3, (ξ i : ℂ) * (z i + w i)) = _
  simp only [mul_add, Finset.sum_add_distrib, frequencyDot]

theorem frequencyDot_smul (ξ : Vec) (a : ℂ) (z : CVec) :
    frequencyDot ξ (a • z) = a * frequencyDot ξ z := by
  change (∑ i : Fin 3, (ξ i : ℂ) * (a * z i)) =
    a * ∑ i : Fin 3, (ξ i : ℂ) * z i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem frequencyDot_sub (ξ : Vec) (z w : CVec) :
    frequencyDot ξ (z - w) = frequencyDot ξ z - frequencyDot ξ w := by
  change (∑ i : Fin 3, (ξ i : ℂ) * (z i - w i)) = _
  simp only [mul_sub, Finset.sum_sub_distrib, frequencyDot]

theorem frequencyDot_complexify (ξ : Vec) :
    frequencyDot ξ (complexify ξ) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
  change (∑ i : Fin 3, (ξ i : ℂ) * (ξ i : ℂ)) =
    ((‖ξ‖ ^ 2 : ℝ) : ℂ)
  rw [EuclideanSpace.real_norm_sq_eq]
  push_cast
  simp only [pow_two]

theorem frequencyDot_eq_inner (ξ : Vec) (z : CVec) :
    frequencyDot ξ z = inner ℂ (complexify ξ) z := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (ξ i : ℂ) * z i = inner ℂ (ξ i : ℂ) (z i)
  rw [RCLike.inner_apply, Complex.conj_ofReal]
  ring

theorem transverseSymbol_eq (ξ : Vec) (z : CVec) :
    transverseSymbol ξ z =
      z - (frequencyDot ξ z / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) • complexify ξ := rfl

theorem transverseSymbol_add (ξ : Vec) (z w : CVec) :
    transverseSymbol ξ (z + w) =
      transverseSymbol ξ z + transverseSymbol ξ w := by
  simp only [transverseSymbol_eq, frequencyDot_add, add_div, add_smul]
  abel

theorem transverseSymbol_smul (ξ : Vec) (a : ℂ) (z : CVec) :
    transverseSymbol ξ (a • z) = a • transverseSymbol ξ z := by
  simp only [transverseSymbol_eq, frequencyDot_smul, mul_div_assoc,
    mul_smul, smul_sub]

/-- The literal transverse formula is complex linear. -/
def transverseLinearMap (ξ : Vec) : CVec →ₗ[ℂ] CVec where
  toFun := transverseSymbol ξ
  map_add' := transverseSymbol_add ξ
  map_smul' := transverseSymbol_smul ξ

theorem complexCross_add (ξ : Vec) (z w : CVec) :
    complexCross ξ (z + w) = complexCross ξ z + complexCross ξ w := by
  ext i
  change crossProduct (fun j : Fin 3 => (ξ j : ℂ))
      ((fun j : Fin 3 => z j) + (fun j : Fin 3 => w j)) i =
    crossProduct (fun j : Fin 3 => (ξ j : ℂ)) (fun j : Fin 3 => z j) i +
      crossProduct (fun j : Fin 3 => (ξ j : ℂ)) (fun j : Fin 3 => w j) i
  exact congrFun ((crossProduct (fun j : Fin 3 => (ξ j : ℂ))).map_add
    (fun j : Fin 3 => z j) (fun j : Fin 3 => w j)) i

theorem complexCross_smul (ξ : Vec) (a : ℂ) (z : CVec) :
    complexCross ξ (a • z) = a • complexCross ξ z := by
  ext i
  change crossProduct (fun j : Fin 3 => (ξ j : ℂ))
      (a • (fun j : Fin 3 => z j)) i =
    (a • crossProduct (fun j : Fin 3 => (ξ j : ℂ)) (fun j : Fin 3 => z j)) i
  exact congrFun ((crossProduct (fun j : Fin 3 => (ξ j : ℂ))).map_smul
    a (fun j : Fin 3 => z j)) i

def complexCrossLinearMap (ξ : Vec) : CVec →ₗ[ℂ] CVec where
  toFun := complexCross ξ
  map_add' := complexCross_add ξ
  map_smul' := complexCross_smul ξ

theorem complexCross_sub (ξ : Vec) (z w : CVec) :
    complexCross ξ (z - w) = complexCross ξ z - complexCross ξ w :=
  (complexCrossLinearMap ξ).map_sub z w

theorem helicalSymbol_add (σ : Fin 2) (ξ : Vec) (z w : CVec) :
    helicalSymbol σ ξ (z + w) =
      helicalSymbol σ ξ z + helicalSymbol σ ξ w := by
  simp only [helicalSymbol, transverseSymbol_add, complexCross_add, smul_add]
  abel

theorem helicalSymbol_smul (σ : Fin 2) (ξ : Vec) (a : ℂ) (z : CVec) :
    helicalSymbol σ ξ (a • z) = a • helicalSymbol σ ξ z := by
  simp only [helicalSymbol, transverseSymbol_smul, complexCross_smul]
  rw [smul_comm (((helicitySign σ : ℝ) : ℂ) * Complex.I / (‖ξ‖ : ℂ))
      a (complexCross ξ z), ← smul_add, smul_comm (1 / 2 : ℂ) a]

/-- The intrinsic helical formula, packaged as its actual linear map. -/
def helicalLinearMap (σ : Fin 2) (ξ : Vec) : CVec →ₗ[ℂ] CVec where
  toFun := helicalSymbol σ ξ
  map_add' := helicalSymbol_add σ ξ
  map_smul' := helicalSymbol_smul σ ξ

theorem helicalSymbol_packetRotate
    (σ : Fin 2) (ξ : Vec) (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (lam t : ℝ) (c : Vec → CVec) :
    helicalSymbol σ ξ (packetRotate β ψ lam t c ξ) =
      packetPhase β ψ lam t ξ • helicalSymbol σ ξ (c ξ) :=
  helicalSymbol_smul σ ξ _ _

theorem norm_helicalSymbol_packetRotate
    (σ : Fin 2) (ξ : Vec) (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (lam t : ℝ) (c : Vec → CVec) :
    ‖helicalSymbol σ ξ (packetRotate β ψ lam t c ξ)‖ =
      ‖helicalSymbol σ ξ (c ξ)‖ := by
  rw [helicalSymbol_packetRotate, norm_smul, norm_packetPhase, one_mul]

theorem helicalPower_eq_of_fourier_phase
    (σ : Fin 2) (u v : Field) (ξ : Vec) (theta : ℝ)
    (h : fourierVelocity v ξ = MethbokeAddon.FDSN.phase theta • fourierVelocity u ξ) :
    helicalPower σ v ξ = helicalPower σ u ξ := by
  simp only [helicalPower, h, helicalSymbol_smul, norm_smul,
    MethbokeAddon.FDSN.norm_phase, one_mul]

theorem frequencyDot_transverseSymbol {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec) :
    frequencyDot ξ (transverseSymbol ξ z) = 0 := by
  have hn : ((‖ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ))
  rw [transverseSymbol_eq, frequencyDot_sub, frequencyDot_smul,
    frequencyDot_complexify, div_mul_cancel₀ _ hn, sub_self]

theorem transverseSymbol_of_frequencyDot_eq_zero
    (ξ : Vec) {z : CVec} (hz : frequencyDot ξ z = 0) :
    transverseSymbol ξ z = z := by
  simp only [transverseSymbol_eq, hz, zero_div, zero_smul, sub_zero]

theorem transverseSymbol_idempotent {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec) :
    transverseSymbol ξ (transverseSymbol ξ z) = transverseSymbol ξ z :=
  transverseSymbol_of_frequencyDot_eq_zero ξ (frequencyDot_transverseSymbol hξ z)

theorem complexCross_complexify (ξ : Vec) :
    complexCross ξ (complexify ξ) = 0 := by
  ext i
  change crossProduct (fun j : Fin 3 => (ξ j : ℂ))
      (fun j : Fin 3 => (ξ j : ℂ)) i = 0
  rw [cross_self]
  rfl

theorem frequencyDot_complexCross (ξ : Vec) (z : CVec) :
    frequencyDot ξ (complexCross ξ z) = 0 := by
  change dotProduct (fun i : Fin 3 => (ξ i : ℂ))
    (crossProduct (fun i : Fin 3 => (ξ i : ℂ)) (fun i : Fin 3 => z i)) = 0
  exact dot_self_cross _ _

theorem transverseSymbol_complexCross (ξ : Vec) (z : CVec) :
    transverseSymbol ξ (complexCross ξ z) = complexCross ξ z :=
  transverseSymbol_of_frequencyDot_eq_zero ξ (frequencyDot_complexCross ξ z)

theorem complexCross_transverseSymbol (ξ : Vec) (z : CVec) :
    complexCross ξ (transverseSymbol ξ z) = complexCross ξ z := by
  rw [transverseSymbol_eq, complexCross_sub, complexCross_smul,
    complexCross_complexify, smul_zero, sub_zero]

theorem complexCross_twice (ξ : Vec) (z : CVec) :
    complexCross ξ (complexCross ξ z) =
      frequencyDot ξ z • complexify ξ - ((‖ξ‖ ^ 2 : ℝ) : ℂ) • z := by
  have hn :
      dotProduct (fun i : Fin 3 => (ξ i : ℂ))
        (fun i : Fin 3 => (ξ i : ℂ)) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) :=
    frequencyDot_complexify ξ
  ext i
  have h := congrFun (cross_cross_eq_smul_sub_smul'
    (fun j : Fin 3 => (ξ j : ℂ)) (fun j : Fin 3 => (ξ j : ℂ))
    (fun j : Fin 3 => z j)) i
  rw [hn] at h
  exact h

/-- The normalized curl symbol; its square is the transverse projection. -/
def helicityOperator (ξ : Vec) (z : CVec) : CVec :=
  (Complex.I / (‖ξ‖ : ℂ)) • complexCross ξ z

theorem helicityOperator_add (ξ : Vec) (z w : CVec) :
    helicityOperator ξ (z + w) = helicityOperator ξ z + helicityOperator ξ w := by
  simp only [helicityOperator, complexCross_add, smul_add]

theorem helicityOperator_smul (ξ : Vec) (a : ℂ) (z : CVec) :
    helicityOperator ξ (a • z) = a • helicityOperator ξ z := by
  simp only [helicityOperator, complexCross_smul]
  exact smul_comm _ _ _

theorem helicalSymbol_eq (σ : Fin 2) (ξ : Vec) (z : CVec) :
    helicalSymbol σ ξ z =
      (1 / 2 : ℂ) •
        (transverseSymbol ξ z + (helicitySign σ : ℂ) • helicityOperator ξ z) := by
  simp only [helicalSymbol, helicityOperator, smul_smul, mul_div_assoc]

theorem transverseSymbol_helicityOperator (ξ : Vec) (z : CVec) :
    transverseSymbol ξ (helicityOperator ξ z) = helicityOperator ξ z := by
  rw [helicityOperator, transverseSymbol_smul, transverseSymbol_complexCross]

theorem helicityOperator_transverseSymbol (ξ : Vec) (z : CVec) :
    helicityOperator ξ (transverseSymbol ξ z) = helicityOperator ξ z := by
  simp only [helicityOperator, complexCross_transverseSymbol]

theorem helicityOperator_sq {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec) :
    helicityOperator ξ (helicityOperator ξ z) = transverseSymbol ξ z := by
  have hn : (‖ξ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hξ)
  simp only [helicityOperator, complexCross_smul, complexCross_twice]
  ext i
  change (Complex.I / (‖ξ‖ : ℂ)) *
      ((Complex.I / (‖ξ‖ : ℂ)) *
        (frequencyDot ξ z * (ξ i : ℂ) - ((‖ξ‖ ^ 2 : ℝ) : ℂ) * z i)) =
    z i - (frequencyDot ξ z / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) * (ξ i : ℂ)
  push_cast
  field_simp [hn] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem helicalSymbol_transverseSymbol
    (σ : Fin 2) {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec) :
    helicalSymbol σ ξ (transverseSymbol ξ z) = helicalSymbol σ ξ z := by
  simp only [helicalSymbol_eq, transverseSymbol_idempotent hξ,
    helicityOperator_transverseSymbol]

theorem helicityOperator_helicalSymbol
    (σ : Fin 2) {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec) :
    helicityOperator ξ (helicalSymbol σ ξ z) =
      (helicitySign σ : ℂ) • helicalSymbol σ ξ z := by
  simp only [helicalSymbol_eq, helicityOperator_smul, helicityOperator_add,
    helicityOperator_transverseSymbol, helicityOperator_sq hξ]
  by_cases hσ : σ = 0 <;> simp only [helicitySign, hσ, ite_true, ite_false,
    Complex.ofReal_one, Complex.ofReal_neg]
  all_goals
    simp only [one_smul, neg_one_smul, smul_add, smul_neg]
    abel

theorem helicalSymbol_helicityOperator
    (σ : Fin 2) {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec) :
    helicalSymbol σ ξ (helicityOperator ξ z) =
      (helicitySign σ : ℂ) • helicalSymbol σ ξ z := by
  rw [helicalSymbol_eq, transverseSymbol_helicityOperator, helicityOperator_sq hξ,
    helicalSymbol_eq]
  by_cases hσ : σ = 0 <;> simp only [helicitySign, hσ, ite_true, ite_false,
    Complex.ofReal_one, Complex.ofReal_neg]
  all_goals
    simp only [one_smul, neg_one_smul, smul_add, smul_neg]
    abel

theorem complexCurl_helicalSymbol
    (σ : Fin 2) {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec) :
    Complex.I • complexCross ξ (helicalSymbol σ ξ z) =
      ((helicitySign σ : ℂ) * (‖ξ‖ : ℂ)) • helicalSymbol σ ξ z := by
  have hn : (‖ξ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hξ)
  calc
    Complex.I • complexCross ξ (helicalSymbol σ ξ z) =
        (‖ξ‖ : ℂ) • helicityOperator ξ (helicalSymbol σ ξ z) := by
      simp only [helicityOperator, smul_smul]
      congr 1
      field_simp [hn] <;> ring
    _ = (‖ξ‖ : ℂ) • ((helicitySign σ : ℂ) • helicalSymbol σ ξ z) := by
      rw [helicityOperator_helicalSymbol σ hξ]
    _ = ((helicitySign σ : ℂ) * (‖ξ‖ : ℂ)) • helicalSymbol σ ξ z := by
      rw [smul_smul, mul_comm]

/-- The actual curl eigenvalue in the fixed 2π Fourier convention. -/
theorem fourierCurl_helicalSymbol
    (σ : Fin 2) {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec) :
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I) •
        complexCross ξ (helicalSymbol σ ξ z) =
      ((helicitySign σ * (2 * Real.pi) * ‖ξ‖ : ℝ) : ℂ) •
        helicalSymbol σ ξ z := by
  rw [mul_smul, complexCurl_helicalSymbol σ hξ, smul_smul]
  congr 1
  push_cast
  ring

theorem helicitySign_mul_self (σ : Fin 2) :
    (helicitySign σ : ℂ) * (helicitySign σ : ℂ) = 1 := by
  unfold helicitySign
  split_ifs <;> norm_num

theorem helicalSymbol_idempotent
    (σ : Fin 2) {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec) :
    helicalSymbol σ ξ (helicalSymbol σ ξ z) = helicalSymbol σ ξ z := by
  calc
    helicalSymbol σ ξ (helicalSymbol σ ξ z) =
        helicalSymbol σ ξ ((1 / 2 : ℂ) •
          (transverseSymbol ξ z + (helicitySign σ : ℂ) • helicityOperator ξ z)) := by
      rw [← helicalSymbol_eq]
    _ = (1 / 2 : ℂ) •
        (helicalSymbol σ ξ z +
          (helicitySign σ : ℂ) • ((helicitySign σ : ℂ) • helicalSymbol σ ξ z)) := by
      rw [helicalSymbol_smul, helicalSymbol_add, helicalSymbol_smul,
        helicalSymbol_transverseSymbol σ hξ, helicalSymbol_helicityOperator σ hξ]
    _ = helicalSymbol σ ξ z := by
      rw [smul_smul, helicitySign_mul_self, one_smul]
      ext i
      change (1 / 2 : ℂ) * ((helicalSymbol σ ξ z) i + (helicalSymbol σ ξ z) i) =
        (helicalSymbol σ ξ z) i
      ring

theorem helicalSymbol_sum (ξ : Vec) (z : CVec) :
    helicalSymbol 0 ξ z + helicalSymbol 1 ξ z = transverseSymbol ξ z := by
  rw [helicalSymbol_eq, helicalSymbol_eq]
  ext i
  change (1 / 2 : ℂ) *
      ((transverseSymbol ξ z) i + (helicitySign 0 : ℂ) * (helicityOperator ξ z) i) +
    (1 / 2 : ℂ) *
      ((transverseSymbol ξ z) i + (helicitySign 1 : ℂ) * (helicityOperator ξ z) i) =
    (transverseSymbol ξ z) i
  norm_num [helicitySign]
  ring

theorem helicalSymbol_zero_one {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec) :
    helicalSymbol 0 ξ (helicalSymbol 1 ξ z) = 0 := by
  have h := congrArg (helicalSymbol 0 ξ) (helicalSymbol_sum ξ z)
  rw [helicalSymbol_add, helicalSymbol_idempotent 0 hξ,
    helicalSymbol_transverseSymbol 0 hξ] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

theorem helicalSymbol_one_zero {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec) :
    helicalSymbol 1 ξ (helicalSymbol 0 ξ z) = 0 := by
  have h := congrArg (helicalSymbol 1 ξ) (helicalSymbol_sum ξ z)
  rw [helicalSymbol_add, helicalSymbol_idempotent 1 hξ,
    helicalSymbol_transverseSymbol 1 hξ] at h
  exact add_right_cancel (h.trans (zero_add _).symm)

theorem transverseSymbol_selfAdjoint (ξ : Vec) (z w : CVec) :
    inner ℂ (transverseSymbol ξ z) w = inner ℂ z (transverseSymbol ξ w) := by
  rw [transverseSymbol_eq, transverseSymbol_eq, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, frequencyDot_eq_inner, frequencyDot_eq_inner]
  simp only [div_eq_mul_inv, map_mul, Complex.conj_inv, Complex.conj_ofReal,
    inner_conj_symm]
  ring

theorem complexCross_skewAdjoint (ξ : Vec) (z w : CVec) :
    inner ℂ (complexCross ξ z) w = -inner ℂ z (complexCross ξ w) := by
  change (∑ i : Fin 3, w i *
      conj (crossProduct (fun j : Fin 3 => (ξ j : ℂ)) (fun j : Fin 3 => z j) i)) =
    -(∑ i : Fin 3,
      crossProduct (fun j : Fin 3 => (ξ j : ℂ)) (fun j : Fin 3 => w j) i * conj (z i))
  simp [Fin.sum_univ_three, cross_apply, map_sub, map_mul, Complex.conj_ofReal]
  ring

theorem helicityOperator_selfAdjoint (ξ : Vec) (z w : CVec) :
    inner ℂ (helicityOperator ξ z) w = inner ℂ z (helicityOperator ξ w) := by
  simp only [helicityOperator, inner_smul_left, inner_smul_right,
    complexCross_skewAdjoint, div_eq_mul_inv, map_mul, Complex.conj_inv,
    Complex.conj_I, Complex.conj_ofReal]
  ring

theorem helicalSymbol_selfAdjoint (σ : Fin 2) (ξ : Vec) (z w : CVec) :
    inner ℂ (helicalSymbol σ ξ z) w = inner ℂ z (helicalSymbol σ ξ w) := by
  simp only [helicalSymbol_eq, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, transverseSymbol_selfAdjoint,
    helicityOperator_selfAdjoint, div_eq_mul_inv, map_mul, Complex.conj_inv,
    map_one, map_ofNat, Complex.conj_ofReal]

theorem helicalSymbol_orthogonal {ξ : Vec} (hξ : ξ ≠ 0) (z w : CVec) :
    inner ℂ (helicalSymbol 0 ξ z) (helicalSymbol 1 ξ w) = 0 := by
  rw [helicalSymbol_selfAdjoint, helicalSymbol_zero_one hξ, inner_zero_right]

theorem helicalSymbol_norm_decomposition {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec) :
    ‖transverseSymbol ξ z‖ ^ 2 =
      ‖helicalSymbol 0 ξ z‖ ^ 2 + ‖helicalSymbol 1 ξ z‖ ^ 2 := by
  rw [← helicalSymbol_sum]
  simpa only [pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (helicalSymbol_orthogonal hξ z z)

theorem helicalSymbol_norm_decomposition_of_solenoidal
    {ξ : Vec} (hξ : ξ ≠ 0) {z : CVec} (hz : frequencyDot ξ z = 0) :
    ‖z‖ ^ 2 = ‖helicalSymbol 0 ξ z‖ ^ 2 + ‖helicalSymbol 1 ξ z‖ ^ 2 := by
  simpa only [transverseSymbol_of_frequencyDot_eq_zero ξ hz] using
    helicalSymbol_norm_decomposition hξ z

end

end MethbokeAddon.FDSNR3

