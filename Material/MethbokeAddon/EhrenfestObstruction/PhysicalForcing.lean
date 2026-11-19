import MethbokeAddon.EhrenfestObstruction.CoefficientError
import MethbokeAddon.WeakFouriermanB.PhysicalNonlinear
import SingularClosure.CriticalGalerkin

/-!
Physical identities and L2 forcing control for the coefficient H1 balance.
Every forcing norm below is a literal physical cube integral. The cutoff and
Leray projection disappear from the pairing by proved Fourier identities.

Prepared source: external cached compiler and axiom audit are still required.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff RealInnerProductSpace

namespace MethbokeAddon.EhrenfestObstruction

noncomputable section

/-- Real finite synthesis uses only nonzero modes and has actual zero mean. -/
theorem finiteSynthesis_meanZero_of_reality
    (N : ℕ) (c : FourierCoeff) (hreal : SpectralReality c) :
    MeanZero (finiteSynthesis N c) := by
  have hi : IntegrableOn (finiteSynthesis N c) unitCube volume :=
    (finiteSynthesis_contDiff N c).continuous.continuousOn.integrableOn_compact
      isCompact_unitCube
  refine ⟨hi, ?_⟩
  ext j
  change spatialMean (finiteSynthesis N c) j = 0
  have hz : datumFourierCoeff (finiteSynthesis N c) 0 j = 0 := by
    rw [criticalGalerkin_datumFourierCoeff_finiteSynthesis N c hreal]
    simp [cutoffCoeff, cutoffModes_zero_not_mem]
  rw [datumFourierCoeff_zero hi] at hz
  exact_mod_cast hz

/-- Direct finite-field specialization of the arbitrary physical nonlinear
absorption theorem, with both quadratic integrals converted by Parseval. -/
theorem FINITE_ERROR_ABSORPTION_FROM_PHYSICAL :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ N : ℕ,
      ∀ c : FourierCoeff,
      (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0) →
      SpectralReality c → SpectralSolenoidal c →
      -2 * coefficientEnstrophyNonlinearPower N c ≤
        ν * coefficientLaplacianSquare N c +
          C / ν ^ 3 * (coefficientDissipation N c) ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := WeakFouriermanB.PHYSICAL_NONLINEAR_ABSORPTION
  refine ⟨C, hC, ?_⟩
  intro ν hν N c hsupp hreal hsol
  have h := hbound ν hν (finiteSynthesis N c)
    (finiteSynthesis_contDiff N c) (finiteSynthesis_periodic N c)
    (finiteSynthesis_meanZero_of_reality N c hreal)
  rw [WeakFouriermanB.physicalLaplacianSquare,
    finite_laplacian_integral_norm_sq N c hreal,
    physicalDissipation, FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL N c hreal] at h
  rw [coefficientEnstrophyNonlinearPower_eq_physical N c hsupp hreal hsol]
  linarith

theorem dissipationRatePairing_cutoff_right
    (N : ℕ) (c f : FourierCoeff) :
    dissipationRatePairing N c (cutoffCoeff N f) =
      dissipationRatePairing N c f := by
  unfold dissipationRatePairing
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  rw [cutoffCoeff_apply_of_mem f hk i]

/-- A solenoidal test coefficient removes the actual modewise Leray map. -/
theorem dissipationRatePairing_leray_right
    (N : ℕ) (c f : FourierCoeff) (hsol : SpectralSolenoidal c) :
    dissipationRatePairing N c (fun k => coefficientLeray k (f k)) =
      dissipationRatePairing N c f := by
  unfold dissipationRatePairing
  apply Finset.sum_congr rfl
  intro k hk
  simp_rw [← mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum,
    ← physical_complex_re_sum, ← physical_complex_re_sum,
    coefficientLeray_pairing k (c k) (f k) (hsol k)]

/-- The exact physical power of a forcing field, with the Laplacian sign. -/
theorem dissipationRatePairing_fourier_eq_physical
    (N : ℕ) (c : FourierCoeff) (F : Field) (hF : Continuous F) :
    dissipationRatePairing N c (datumFourierCoeff F) =
      -2 * (∫ x in unitCube,
        inner ℝ (laplacian (finiteSynthesis N c) x) (F x)) := by
  rw [finiteSynthesis_laplacian,
    integral_finiteSynthesis_pairing N (laplacianCoefficient c) F hF]
  unfold dissipationRatePairing
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  simp [laplacianCoefficient, laplacianFrequency, Complex.star_def,
    Complex.mul_re, Complex.mul_im] <;> ring

/-- Pointwise Young inequality with its exact coefficient; no square roots. -/
theorem physical_inner_young (δ : ℝ) (hδ : 0 < δ) (a b : Vec) :
    -2 * inner ℝ a b ≤ δ * ‖a‖ ^ 2 + ‖b‖ ^ 2 / δ := by
  have hsq : 0 ≤ inner ℝ (δ • a + b) (δ • a + b) :=
    real_inner_self_nonneg
  rw [real_inner_add_add_self] at hsq
  simp only [real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq] at hsq
  have hdiv : (‖b‖ ^ 2 / δ) * δ = ‖b‖ ^ 2 :=
    div_mul_cancel₀ _ hδ.ne'
  apply (mul_le_mul_right hδ).mp
  nlinarith

/-- Integrating Young gives literal L2 forcing control on the physical cube. -/
theorem physical_integral_inner_young
    (δ : ℝ) (hδ : 0 < δ) (a b : Field)
    (ha : Continuous a) (hb : Continuous b) :
    -2 * (∫ x in unitCube, inner ℝ (a x) (b x)) ≤
      δ * (∫ x in unitCube, ‖a x‖ ^ 2) +
        (∫ x in unitCube, ‖b x‖ ^ 2) / δ := by
  have hi : IntegrableOn (fun x => inner ℝ (a x) (b x)) unitCube volume :=
    (ha.inner hb).continuousOn.integrableOn_compact isCompact_unitCube
  have ha2 : IntegrableOn (fun x => ‖a x‖ ^ 2) unitCube volume :=
    (ha.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have hb2 : IntegrableOn (fun x => ‖b x‖ ^ 2) unitCube volume :=
    (hb.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  calc
    _ = ∫ x in unitCube, -2 * inner ℝ (a x) (b x) :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ x in unitCube, δ * ‖a x‖ ^ 2 + ‖b x‖ ^ 2 / δ :=
      integral_mono (hi.const_mul (-2))
        ((ha2.const_mul δ).add (hb2.div_const δ))
        (fun x => physical_inner_young δ hδ (a x) (b x))
    _ = _ := by
      rw [integral_add (ha2.const_mul δ) (hb2.div_const δ),
        integral_const_mul, integral_div]

/-- Projected physical forcing costs its own L2 square and an arbitrarily
chosen positive share of the error's Laplacian square. -/
theorem dissipationRatePairing_projected_forcing_le
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c)
    (F : Field) (hF : Continuous F) :
    dissipationRatePairing N c
        (cutoffCoeff N (fun k => coefficientLeray k (datumFourierCoeff F k))) ≤
      δ * coefficientLaplacianSquare N c +
        (∫ x in unitCube, ‖F x‖ ^ 2) / δ := by
  rw [dissipationRatePairing_cutoff_right,
    dissipationRatePairing_leray_right N c _ hsol,
    dissipationRatePairing_fourier_eq_physical N c F hF]
  have h := physical_integral_inner_young δ hδ
    (laplacian (finiteSynthesis N c)) F
    (laplacian_contDiff _ (finiteSynthesis_contDiff N c)).continuous hF
  rw [finite_laplacian_integral_norm_sq N c hreal] at h
  exact h

/-- The physical forced H1 estimate leaves half the viscous term available.
The equation is literal, and the only inhomogeneous term in the bound is the
actual L2 square of its physical forcing field. -/
theorem PHYSICAL_FORCED_ERROR_ENSTROPHY_INEQUALITY :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ N : ℕ,
      ∀ c : ℝ → FourierCoeff, ∀ F : Field, Continuous F →
      ∀ s : Set ℝ, ∀ t : ℝ,
      (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c t k i = 0) →
      SpectralReality (c t) → SpectralSolenoidal (c t) →
      (∀ k ∈ cutoffModes N, ∀ i : Fin 3,
        HasDerivWithinAt (fun r => c r k i)
          (galerkinRhs ν N (c t) k i +
            cutoffCoeff N
              (fun l => coefficientLeray l (datumFourierCoeff F l)) k i) s t) →
      ∃ d : ℝ,
        HasDerivWithinAt (fun r => coefficientDissipation N (c r)) d s t ∧
        d + (ν / 2) * coefficientLaplacianSquare N (c t) ≤
          C / ν ^ 3 * (coefficientDissipation N (c t)) ^ 3 +
            (2 / ν) * (∫ x in unitCube, ‖F x‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := FINITE_ERROR_ABSORPTION_FROM_PHYSICAL
  refine ⟨C, hC, ?_⟩
  intro ν hν N c F hF s t hsupp hreal hsol heq
  let f : FourierCoeff :=
    cutoffCoeff N (fun k => coefficientLeray k (datumFourierCoeff F k))
  refine ⟨(-2 * ν) * coefficientLaplacianSquare N (c t) -
    2 * coefficientEnstrophyNonlinearPower N (c t) +
    dissipationRatePairing N (c t) f,
    forced_coefficient_dissipation_identity ν N c f heq, ?_⟩
  have hself := hbound ν hν N (c t) hsupp hreal hsol
  have hforce := dissipationRatePairing_projected_forcing_le
    (ν / 2) (by positivity) N (c t) hreal hsol F hF
  change dissipationRatePairing N (c t) f ≤
    (ν / 2) * coefficientLaplacianSquare N (c t) +
      (∫ x in unitCube, ‖F x‖ ^ 2) / (ν / 2) at hforce
  have hdiv : (∫ x in unitCube, ‖F x‖ ^ 2) / (ν / 2) =
      (2 / ν) * (∫ x in unitCube, ‖F x‖ ^ 2) := by
    field_simp [hν.ne'] <;> ring
  rw [hdiv] at hforce
  linarith

end

end MethbokeAddon.EhrenfestObstruction
