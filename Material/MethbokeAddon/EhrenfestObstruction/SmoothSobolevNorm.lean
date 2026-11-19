import SingularClosure.SmoothDatumSobolev

/-!
# Explicit smooth-datum Sobolev norm bounds

Source-prepared candidates: no local Lean execution or acceptance claim.
The estimate is extracted from the actual Fourier-decay membership proof.
-/

set_option autoImplicit false

open SingularClosure
open scoped BigOperators ContDiff ENNReal

namespace MethbokeAddon.EhrenfestObstruction
noncomputable section

/-- Uniform finite weighted-square bound for actual smooth-datum coefficients. -/
theorem smooth_datum_finite_weighted_sum_le (s : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (t : Finset FourierIndex) :
    (∑ ki ∈ t, ‖sobolevWeightedCoeff s (datumFourierCoeff a) ki‖ ^ 2) ≤
      3 * smoothDatumDecayConstant s a ^ 2 * latticeSobolevConstant := by
  classical
  have hsub : t ⊆ (t.image Prod.fst).product (Finset.univ : Finset (Fin 3)) := by
    intro ki hki
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨ki, hki, rfl⟩, Finset.mem_univ _⟩
  have hsum :
      (∑ k ∈ t.image Prod.fst, (torusSobolevWeight k)⁻¹ ^ 4) ≤
        latticeSobolevConstant := by
    have h := Summable.sum_le_tsum (t.image Prod.fst) (fun k _ => by positivity)
      summable_torusSobolevWeight_inv_four
    unfold latticeSobolevConstant
    linarith
  calc
    _ ≤ ∑ ki ∈ t, smoothDatumDecayConstant s a ^ 2 *
        (torusSobolevWeight ki.1)⁻¹ ^ 4 :=
      Finset.sum_le_sum (fun ki _ => smooth_datum_weightedCoeff_sq_le s a ha hp ki)
    _ ≤ ∑ ki ∈ (t.image Prod.fst).product (Finset.univ : Finset (Fin 3)),
        smoothDatumDecayConstant s a ^ 2 * (torusSobolevWeight ki.1)⁻¹ ^ 4 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ki _ _ => by positivity)
    _ = 3 * smoothDatumDecayConstant s a ^ 2 *
        ∑ k ∈ t.image Prod.fst, (torusSobolevWeight k)⁻¹ ^ 4 := by
      simp [Finset.sum_product, Finset.mul_sum, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

/-- The actual smooth-datum Hilbert norm is controlled by its explicit decay constant. -/
theorem smoothDatumSobolev_norm_le (s : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    ‖smoothDatumSobolev s a ha hp‖ ≤
      Real.sqrt (3 * latticeSobolevConstant) * smoothDatumDecayConstant s a := by
  have hC : 0 ≤ smoothDatumDecayConstant s a := smoothDatumDecayConstant_nonneg s a
  have hL : 0 ≤ 3 * latticeSobolevConstant :=
    mul_nonneg (by norm_num) latticeSobolevConstant_pos.le
  have hsq :
      (Real.sqrt (3 * latticeSobolevConstant) * smoothDatumDecayConstant s a) ^ 2 =
        3 * smoothDatumDecayConstant s a ^ 2 * latticeSobolevConstant := by
    rw [mul_pow, Real.sq_sqrt hL]
    ring
  change ‖torusSobolevRepr s (smoothDatumSobolev s a ha hp)‖ ≤ _
  apply lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) (by norm_num)
    (mul_nonneg (Real.sqrt_nonneg _) hC)
  intro t
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, hsq]
  simpa only [torusSobolevRepr_apply, smoothDatumSobolev_coeff, sobolevWeightedCoeff]
    using smooth_datum_finite_weighted_sum_le s a ha hp t

/-- Squared-norm form of the extracted smooth-datum estimate. -/
theorem smoothDatumSobolev_norm_sq_le (s : ℕ) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    ‖smoothDatumSobolev s a ha hp‖ ^ 2 ≤
      3 * smoothDatumDecayConstant s a ^ 2 * latticeSobolevConstant := by
  have hL : 0 ≤ 3 * latticeSobolevConstant :=
    mul_nonneg (by norm_num) latticeSobolevConstant_pos.le
  calc
    _ ≤ (Real.sqrt (3 * latticeSobolevConstant) * smoothDatumDecayConstant s a) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (smoothDatumSobolev_norm_le s a ha hp) 2
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt hL]
      ring

end
end MethbokeAddon.EhrenfestObstruction
