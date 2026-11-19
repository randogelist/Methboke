import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Pointwise transport--multiplication commutator on actual differentiable
functions. The zero-order coefficient cancels identically. This is the
algebraic core of the operator translation, not an L2 domain, self-adjointness
or unitary-group theorem. Prepared for external verification only.
-/

set_option autoImplicit false

namespace MethbokeAddon.EhrenfestObstruction
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Transport plus a zero-order multiplication coefficient. -/
def transportExpression (b : E → E) (z : E → ℂ) (f : E → ℂ) (x : E) : ℂ :=
  fderiv ℝ f x (b x) + z x * f x

/-- The formal Hamiltonian expression with the fixed negative-i convention. -/
def hamiltonianExpression (hbar : ℝ) (b : E → E) (z : E → ℂ)
    (f : E → ℂ) (x : E) : ℂ :=
  -Complex.I * (hbar : ℂ) * transportExpression b z f x

/-- The zeroth-order coefficient cancels from the transport commutator. -/
theorem transport_multiplication_commutator
    (b : E → E) (z g ψ : E → ℂ) (x : E)
    (hg : DifferentiableAt ℝ g x) (hψ : DifferentiableAt ℝ ψ x) :
    transportExpression b z (fun y => g y * ψ y) x -
        g x * transportExpression b z ψ x =
      fderiv ℝ g x (b x) * ψ x := by
  unfold transportExpression
  rw [fderiv_fun_mul hg hψ]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

/-- Unnormalized exact commutator of the formal Hamiltonian expression. -/
theorem hamiltonian_multiplication_commutator
    (hbar : ℝ) (b : E → E) (z g ψ : E → ℂ) (x : E)
    (hg : DifferentiableAt ℝ g x) (hψ : DifferentiableAt ℝ ψ x) :
    hamiltonianExpression hbar b z (fun y => g y * ψ y) x -
        g x * hamiltonianExpression hbar b z ψ x =
      -Complex.I * (hbar : ℂ) * (fderiv ℝ g x (b x) * ψ x) := by
  unfold hamiltonianExpression
  calc
    _ = -Complex.I * (hbar : ℂ) *
        (transportExpression b z (fun y => g y * ψ y) x -
          g x * transportExpression b z ψ x) := by ring
    _ = _ := by rw [transport_multiplication_commutator b z g ψ x hg hψ]

/-- Exact pointwise Heisenberg normalization; hbar cancels from the rate. -/
theorem normalized_hamiltonian_commutator
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (b : E → E) (z g ψ : E → ℂ) (x : E)
    (hg : DifferentiableAt ℝ g x) (hψ : DifferentiableAt ℝ ψ x) :
    (Complex.I / (hbar : ℂ)) *
        (hamiltonianExpression hbar b z (fun y => g y * ψ y) x -
          g x * hamiltonianExpression hbar b z ψ x) =
      fderiv ℝ g x (b x) * ψ x := by
  rw [hamiltonian_multiplication_commutator hbar b z g ψ x hg hψ]
  have hne : (hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hbar_pos)
  have hfactor : (Complex.I / (hbar : ℂ)) * (-Complex.I * (hbar : ℂ)) = 1 := by
    simp only [div_eq_mul_inv]
    calc
      _ = -(Complex.I * Complex.I) * ((hbar : ℂ) * (hbar : ℂ)⁻¹) := by ring
      _ = 1 := by rw [Complex.I_mul_I, mul_inv_cancel₀ hne]; norm_num
  rw [← mul_assoc, hfactor, one_mul]

end
end MethbokeAddon.EhrenfestObstruction
