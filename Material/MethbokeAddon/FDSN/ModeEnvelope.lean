import MethbokeAddon.FDSN.ModalEnergy
import SingularClosure.LerayL2Contraction
import SingularClosure.SmoothDatumSobolev
import Mathlib.Analysis.ODE.Gronwall

/-!
# Uniform weighted modal bounds from scalar energy inequalities

The scalar propagation takes place on closed intervals strictly before the
terminal time. No value or regularity at the terminal time is required.
The Leray estimate is derived from the native finite-dimensional energy
contraction and applies to the actual forcing coefficients, including zero.
-/

set_option autoImplicit false

open Set Filter SingularClosure
open scoped BigOperators Topology

namespace MethbokeAddon.FDSN

noncomputable section

theorem uniform_energy_bound_of_deriv_le
    {E : ℝ → ℝ} {a T A G ρ : ℝ}
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (hd : ∀ r ∈ Ico a T, DifferentiableAt ℝ E r)
    (hinit : E a ≤ A * ρ)
    (hbound : ∀ r ∈ Ico a T, deriv E r ≤ E r + G * ρ)
    (t : ℝ) (ht : t ∈ Ico a T) :
    E t ≤ ((A + G) * Real.exp (T - a)) * ρ := by
  have hc : ContinuousOn E (Icc a t) := by
    intro r hr
    exact (hd r ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩).continuousAt.continuousWithinAt
  have hgr : E t ≤ gronwallBound (A * ρ) 1 (G * ρ) (t - a) := by
    refine le_gronwallBound_of_liminf_deriv_right_le
      (f' := deriv E) hc ?_ hinit ?_ t ⟨ht.1, le_rfl⟩
    · intro r hr q hq
      have hdr := (hd r ⟨hr.1, lt_trans hr.2 ht.2⟩).hasDerivAt
      simpa only [slope_def_module, smul_eq_mul] using
        hdr.hasDerivWithinAt.liminf_right_slope_le hq
    · intro r hr
      simpa only [one_mul] using hbound r ⟨hr.1, lt_trans hr.2 ht.2⟩
  have hexp : Real.exp (t - a) ≤ Real.exp (T - a) :=
    Real.exp_le_exp.mpr (sub_le_sub_right ht.2.le a)
  have hcoef : 0 ≤ (A + G) * ρ := mul_nonneg (add_nonneg hA hG) hρ
  calc
    E t ≤ gronwallBound (A * ρ) 1 (G * ρ) (t - a) := hgr
    _ ≤ ((A + G) * ρ) * Real.exp (t - a) := by
      simp only [gronwallBound, one_ne_zero, if_false, one_mul, div_one]
      nlinarith [mul_nonneg hG hρ]
    _ ≤ ((A + G) * ρ) * Real.exp (T - a) := mul_le_mul_of_nonneg_left hexp hcoef
    _ = ((A + G) * Real.exp (T - a)) * ρ := by ring

theorem complex_normSq_le_of_weighted_norm_le {z : ℂ} {C r : ℝ}
    (h : ‖z‖ ≤ C * r ^ 4) : Complex.normSq z ≤ C ^ 2 * r ^ 8 := by
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖z‖ ^ 2 ≤ (C * r ^ 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg z) h 2
    _ = C ^ 2 * r ^ 8 := by ring

theorem coefficientLeray_component_normSq_le_envelope
    (k : Frequency) (v : Fin 3 → ℂ) (C : ℝ)
    (hv : ∀ j : Fin 3, ‖v j‖ ≤ C * (torusSobolevWeight k)⁻¹ ^ 4)
    (i : Fin 3) :
    Complex.normSq (coefficientLeray k v i) ≤
      (3 * C ^ 2) * (torusSobolevWeight k)⁻¹ ^ 8 := by
  calc
    Complex.normSq (coefficientLeray k v i) ≤
        ∑ j : Fin 3, Complex.normSq (coefficientLeray k v j) :=
      Finset.single_le_sum (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ j : Fin 3, Complex.normSq (v j) := coefficientLeray_energy_le k v
    _ ≤ ∑ _j : Fin 3, C ^ 2 * (torusSobolevWeight k)⁻¹ ^ 8 :=
      Finset.sum_le_sum (fun j _ => complex_normSq_le_of_weighted_norm_le (hv j))
    _ = (3 * C ^ 2) * (torusSobolevWeight k)⁻¹ ^ 8 := by simp; ring

theorem weighted_norm_le_of_normSq_le {z : ℂ} {B r : ℝ}
    (hB : 0 ≤ B) (h : Complex.normSq z ≤ B * r ^ 8) :
    ‖z‖ ≤ Real.sqrt B * r ^ 4 := by
  have hright : 0 ≤ Real.sqrt B * r ^ 4 := by positivity
  apply (sq_le_sq₀ (norm_nonneg z) hright).mp
  calc
    ‖z‖ ^ 2 = Complex.normSq z := (Complex.normSq_eq_norm_sq z).symm
    _ ≤ B * r ^ 8 := h
    _ = (Real.sqrt B * r ^ 4) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hB]
      ring

end

end MethbokeAddon.FDSN
