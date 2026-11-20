import SingularClosure.FourierProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Triad-free cancellation for the native infinite transport coefficients

The only geometry premise is absence of a nonzero, noncollinear active
triad. The cancellation itself is derived. The H0 type supplies the genuine
convolution summability through `fourierTensorCoefficient_summable`.
The spatial mean is retained and its contribution is shown purely imaginary.
-/

noncomputable section

open SingularClosure
open scoped BigOperators

namespace MethbokeAddon.FDSN

/-- For a nonzero first frequency, this is the usual real collinearity relation. -/
def FrequencyParallel (p q : Frequency) : Prop :=
  ∃ r : ℝ, ∀ j : Fin 3, (q j : ℝ) = r * (p j : ℝ)

/-- An active, noncollinear resonant triple of nonzero integer frequencies. -/
def HasActiveNoncollinearTriad (c : FourierCoeff) : Prop :=
  ∃ p q : Frequency,
    p ≠ 0 ∧ q ≠ 0 ∧ p + q ≠ 0 ∧
    c p ≠ 0 ∧ c q ≠ 0 ∧ c (p + q) ≠ 0 ∧ ¬ FrequencyParallel p q

/-- One input-frequency contribution to the actual divergence-form transport. -/
def transportModeTerm (c : FourierCoeff) (k p : Frequency) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, derivativeSymbol j k * c p j * c (k - p) i

/-- The mean-advection factor at a given output frequency. -/
def meanTransportFactor (c : FourierCoeff) (k : Frequency) : ℂ :=
  ∑ j : Fin 3, derivativeSymbol j k * c 0 j

theorem transportModeTerm_factored (c : FourierCoeff) (k p : Frequency) (i : Fin 3) :
    transportModeTerm c k p i =
      (∑ j : Fin 3, derivativeSymbol j k * c p j) * c (k - p) i := by
  simp only [transportModeTerm, Finset.sum_mul]

theorem transportModeTerm_zero_output (c : FourierCoeff) (p : Frequency) (i : Fin 3) :
    transportModeTerm c 0 p i = 0 := by
  simp [transportModeTerm, derivativeSymbol]

theorem transportModeTerm_zero_left (c : FourierCoeff) (k p : Frequency) (i : Fin 3)
    (hp : c p = 0) : transportModeTerm c k p i = 0 := by
  simp [transportModeTerm, hp]

theorem transportModeTerm_zero_right (c : FourierCoeff) (k p : Frequency) (i : Fin 3)
    (hq : c (k - p) = 0) : transportModeTerm c k p i = 0 := by
  simp [transportModeTerm, hq]

theorem transportModeTerm_mean (c : FourierCoeff) (k : Frequency) (i : Fin 3) :
    transportModeTerm c k 0 i = meanTransportFactor c k * c k i := by
  rw [transportModeTerm_factored]
  simp only [meanTransportFactor, sub_zero]

theorem collinear_derivativeSum_zero (c : FourierCoeff)
    (hsol : SpectralSolenoidal c) (p q : Frequency) (hpq : FrequencyParallel p q) :
    (∑ j : Fin 3, derivativeSymbol j (p + q) * c p j) = 0 := by
  obtain ⟨r, hr⟩ := hpq
  have hder (j : Fin 3) : derivativeSymbol j (p + q) =
      (1 + (r : ℂ)) * derivativeSymbol j p := by
    have hq : (q j : ℂ) = (r : ℂ) * (p j : ℂ) := by exact_mod_cast hr j
    simp only [derivativeSymbol, Pi.add_apply, Int.cast_add]
    push_cast
    rw [hq]
    ring
  calc
    (∑ j : Fin 3, derivativeSymbol j (p + q) * c p j) =
        (1 + (r : ℂ)) * (∑ j : Fin 3, derivativeSymbol j p * c p j) := by
      simp only [hder, Finset.mul_sum, mul_assoc]
    _ = 0 := by rw [solenoidal_derivativeSymbol_sum c hsol p, mul_zero]

/-- With a nonzero output coefficient, every nonzero input-frequency
contribution vanishes if no active noncollinear triad exists. -/
theorem transportModeTerm_nonzero_input_zero
    (c : FourierCoeff) (hsol : SpectralSolenoidal c)
    (htriad : ¬ HasActiveNoncollinearTriad c)
    (k p : Frequency) (i : Fin 3) (hout : c k ≠ 0) (hp : p ≠ 0) :
    transportModeTerm c k p i = 0 := by
  classical
  by_cases hk : k = 0
  · subst k
    exact transportModeTerm_zero_output c p i
  by_cases hcp : c p = 0
  · exact transportModeTerm_zero_left c k p i hcp
  by_cases hcq : c (k - p) = 0
  · exact transportModeTerm_zero_right c k p i hcq
  by_cases hq : k - p = 0
  · have hkp : k = p := sub_eq_zero.mp hq
    subst k
    rw [transportModeTerm_factored, solenoidal_derivativeSymbol_sum c hsol p, zero_mul]
  have hsum : p + (k - p) = k := by rw [add_comm, sub_add_cancel]
  have hpar : FrequencyParallel p (k - p) := by
    by_contra hn
    apply htriad
    refine ⟨p, k - p, hp, hq, ?_, hcp, hcq, ?_, hn⟩
    · simpa only [hsum] using hk
    · simpa only [hsum] using hout
  have hd := collinear_derivativeSum_zero c hsol p (k - p) hpar
  rw [hsum] at hd
  rw [transportModeTerm_factored, hd, zero_mul]

/-- The actual infinite native transport coefficient is the sum of its
input-frequency terms. Summability is derived from H0, not assumed. -/
theorem fullTransportCoefficients_hasSum (c : TorusSobolev 0)
    (k : Frequency) (i : Fin 3) :
    HasSum (fun p : Frequency => transportModeTerm c.val k p i)
      (fullTransportCoefficients c k i) := by
  have hs : HasSum
      (fun p : Frequency => ∑ j : Fin 3,
        derivativeSymbol j k * (c.val p j * c.val (k - p) i))
      (∑ j : Fin 3, derivativeSymbol j k *
        (∑' p : Frequency, c.val p j * c.val (k - p) i)) := by
    exact hasSum_sum (fun j _ =>
      (fourierTensorCoefficient_summable k j i c c).hasSum.mul_left (derivativeSymbol j k))
  simpa only [transportModeTerm, fullTransportCoefficients,
    divergenceTransportCoefficient_apply, mul_assoc] using hs

/-- On an active output mode, triad-free transport is exactly mean advection. -/
theorem fullTransportCoefficients_eq_mean
    (c : TorusSobolev 0) (hsol : SpectralSolenoidal c.val)
    (htriad : ¬ HasActiveNoncollinearTriad c.val)
    (k : Frequency) (i : Fin 3) (hout : c.val k ≠ 0) :
    fullTransportCoefficients c k i = meanTransportFactor c.val k * c.val k i := by
  have hs : HasSum (fun p : Frequency => transportModeTerm c.val k p i)
      (transportModeTerm c.val k 0 i) :=
    hasSum_single 0 (fun p hp =>
      transportModeTerm_nonzero_input_zero c.val hsol htriad k p i hout hp)
  calc
    fullTransportCoefficients c k i = transportModeTerm c.val k 0 i :=
      (fullTransportCoefficients_hasSum c k i).unique hs
    _ = meanTransportFactor c.val k * c.val k i := transportModeTerm_mean c.val k i

theorem spectralReality_mean_im_zero (c : FourierCoeff) (hreal : SpectralReality c)
    (j : Fin 3) : (c 0 j).im = 0 := by
  have h : c 0 j = star (c 0 j) := by simpa only [neg_zero] using hreal 0 j
  have him := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

theorem meanTransportFactor_re_zero (c : FourierCoeff) (hreal : SpectralReality c)
    (k : Frequency) : (meanTransportFactor c k).re = 0 := by
  unfold meanTransportFactor
  rw [Complex.re_sum]
  apply Finset.sum_eq_zero
  intro j _
  simp [derivativeSymbol, Complex.mul_re, Complex.mul_im,
    spectralReality_mean_im_zero c hreal j]

theorem real_star_mul_imaginary (z a : ℂ) (ha : a.re = 0) :
    (star z * (a * z)).re = 0 := by
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, ha]
  ring

/-- The real nonlinear energy transfer of each component of every mode
vanishes in the absence of an active noncollinear triad. -/
theorem triad_free_modal_transfer_zero
    (c : TorusSobolev 0) (hreal : SpectralReality c.val)
    (hsol : SpectralSolenoidal c.val)
    (htriad : ¬ HasActiveNoncollinearTriad c.val)
    (k : Frequency) (i : Fin 3) :
    (star (c.val k i) * fullTransportCoefficients c k i).re = 0 := by
  classical
  by_cases hout : c.val k = 0
  · have hi : c.val k i = 0 := congrFun hout i
    simp [hi]
  rw [fullTransportCoefficients_eq_mean c hsol htriad k i hout]
  exact real_star_mul_imaginary _ _ (meanTransportFactor_re_zero c.val hreal k)

/-- Every finite real weighted modal sum has zero nonlinear transfer. -/
theorem triad_free_finite_weighted_transfer_zero
    (c : TorusSobolev 0) (hreal : SpectralReality c.val)
    (hsol : SpectralSolenoidal c.val)
    (htriad : ¬ HasActiveNoncollinearTriad c.val)
    (S : Finset Frequency) (w : Frequency → ℝ) :
    (∑ k ∈ S, w k * ∑ i : Fin 3,
      (star (c.val k i) * fullTransportCoefficients c k i).re) = 0 := by
  simp only [triad_free_modal_transfer_zero c hreal hsol htriad,
    Finset.sum_const_zero, mul_zero]

end MethbokeAddon.FDSN
