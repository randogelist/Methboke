import MethbokeAddon.EhrenfestObstruction.Definitions
import MethbokeAddon.WeakFouriermanB.InitialFrontAdmission
import SingularClosure.GalerkinInvariant
import SingularClosure.InitialFourier

/-!
Algebraic state and reconstruction bounds for the actual canonical Galerkin
error against the Fourier cutoff of a physical reference field.

These are coefficient identities and inequalities. No error evolution,
uniform error bound, or NSE obstruction is asserted by this module.
Prepared source only; external cached verification is required.
-/

set_option autoImplicit false

open Set Filter SingularClosure
open MethbokeAddon.WeakFouriermanB
open scoped BigOperators

namespace MethbokeAddon.EhrenfestObstruction

noncomputable section

theorem complex_normSq_add_le_twice (z w : ℂ) :
    Complex.normSq (z + w) ≤ 2 * Complex.normSq z + 2 * Complex.normSq w := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im - w.im)]

/-- Weighted coefficient triangle inequality for the actual H1 square. -/
theorem coefficientDissipation_add_le_twice (N : ℕ) (c v : FourierCoeff) :
    coefficientDissipation N (c + v) ≤
      2 * coefficientDissipation N c + 2 * coefficientDissipation N v := by
  unfold coefficientDissipation
  calc
    _ ≤ (∑ k ∈ cutoffModes N,
        (∑ i : Fin 3,
          (2 * ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) * Complex.normSq (c k i)) +
          2 * ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) * Complex.normSq (v k i))))) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro i hi
      have hfreq : 0 ≤ (galerkinFreqSq k : ℝ) := by
        exact_mod_cast galerkinFreqSq_nonneg k
      have hweight : 0 ≤ (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) :=
        mul_nonneg (sq_nonneg _) hfreq
      have hh := mul_le_mul_of_nonneg_left
        (complex_normSq_add_le_twice (c k i) (v k i)) hweight
      simpa only [Pi.add_apply] using (by nlinarith [hh] :
        (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) *
          Complex.normSq (c k i + v k i) ≤
          2 * ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) * Complex.normSq (c k i)) +
          2 * ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) * Complex.normSq (v k i)))
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- Reconstructing the Galerkin state from error plus reference. -/
theorem coefficientDissipation_le_error_plus_reference
    (N : ℕ) (c v : FourierCoeff) :
    coefficientDissipation N c ≤
      2 * coefficientDissipation N (c - v) + 2 * coefficientDissipation N v := by
  simpa only [sub_add_cancel] using coefficientDissipation_add_le_twice N (c - v) v

theorem coefficientDissipation_cutoff_eq (N : ℕ) (c : FourierCoeff) :
    coefficientDissipation N (cutoffCoeff N c) = coefficientDissipation N c := by
  unfold coefficientDissipation
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  rw [cutoffCoeff_apply_of_mem c hk i]

theorem coefficientDissipation_zero_eq (N : ℕ) :
    coefficientDissipation N (0 : FourierCoeff) = 0 := by
  simp [coefficientDissipation]

theorem spectralReality_sub {c v : FourierCoeff}
    (hc : SpectralReality c) (hv : SpectralReality v) : SpectralReality (c - v) := by
  intro k i
  change c (-k) i - v (-k) i = star (c k i - v k i)
  rw [hc k i, hv k i, star_sub]

theorem spectralSolenoidal_sub {c v : FourierCoeff}
    (hc : SpectralSolenoidal c) (hv : SpectralSolenoidal v) :
    SpectralSolenoidal (c - v) := by
  intro k
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, hc k, hv k, sub_self]

/-- The literal coefficient error, with the actual cutoff `n+1`. -/
def canonicalErrorCoeff (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (u : Velocity) (n : ℕ) (t : ℝ) : FourierCoeff :=
  (canonicalFamily ν hν a n).coeff t - cutoffCoeff (n + 1) (datumFourierCoeff (u t))

theorem canonicalErrorCoeff_initial
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (u : Velocity)
    (hinit : u 0 = a.val) (n : ℕ) : canonicalErrorCoeff ν hν a u n 0 = 0 := by
  funext k i
  simp only [canonicalErrorCoeff, Pi.sub_apply]
  rw [(canonicalFamily ν hν a n).initial k i, hinit]
  simp only [cutoffCoeff, Pi.zero_apply, sub_self]

theorem canonicalErrorCoeff_initial_front
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (S : ℝ) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a.val u p) (n : ℕ) :
    canonicalErrorCoeff ν hν a u n 0 = 0 :=
  canonicalErrorCoeff_initial ν hν a u H.initial n

theorem canonicalErrorCoeff_support
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (u : Velocity)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (k : Frequency) (hk : k ∉ cutoffModes (n + 1)) (i : Fin 3) :
    canonicalErrorCoeff ν hν a u n t k i = 0 := by
  simp only [canonicalErrorCoeff, Pi.sub_apply]
  rw [(canonicalFamily ν hν a n).mode_support t ht k hk i,
    cutoffCoeff_apply_of_not_mem (datumFourierCoeff (u t)) hk i, sub_self]

theorem canonicalErrorCoeff_reality
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (u : Velocity)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    SpectralReality (canonicalErrorCoeff ν hν a u n t) :=
  spectralReality_sub ((canonicalFamily ν hν a n).real_symmetry t ht)
    (cutoffCoeff_preserves_reality (n + 1) (datumFourierCoeff_reality (u t)))

theorem canonicalErrorCoeff_solenoidal
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (u : Velocity)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (hu : SmoothSigmaZero (u t)) :
    SpectralSolenoidal (canonicalErrorCoeff ν hν a u n t) :=
  spectralSolenoidal_sub ((canonicalFamily ν hν a n).solenoidal t ht)
    (cutoffCoeff_preserves_solenoidal (n + 1) (smoothSigmaZero_fourier_solenoidal hu))

theorem canonicalErrorCoeff_solenoidal_front
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (S : ℝ) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a.val u p)
    (n : ℕ) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) S) :
    SpectralSolenoidal (canonicalErrorCoeff ν hν a u n t) :=
  canonicalErrorCoeff_solenoidal ν hν a u n t ht.1
    (initial_front_smooth_slices ν S a.val u p H t ht)

theorem canonical_error_initial_dissipation
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (u : Velocity)
    (hinit : u 0 = a.val) (n : ℕ) :
    coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n 0) = 0 := by
  rw [canonicalErrorCoeff_initial ν hν a u hinit n, coefficientDissipation_zero_eq]

/-- The half-enstrophy normalization cancels the factor two in the square
triangle estimate. This is valid at every time without an evolution premise. -/
theorem canonical_enstrophy_le_error_plus_reference
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (u : Velocity) (n : ℕ) (t : ℝ) :
    canonicalEnstrophy ν hν a n t ≤
      coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n t) +
        coefficientDissipation (n + 1) (datumFourierCoeff (u t)) := by
  have h := coefficientDissipation_le_error_plus_reference (n + 1)
    ((canonicalFamily ν hν a n).coeff t)
    (cutoffCoeff (n + 1) (datumFourierCoeff (u t)))
  rw [coefficientDissipation_cutoff_eq] at h
  change coefficientDissipation (n + 1) ((canonicalFamily ν hν a n).coeff t) / 2 ≤ _
  change coefficientDissipation (n + 1) ((canonicalFamily ν hν a n).coeff t) ≤
    2 * coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n t) +
      2 * coefficientDissipation (n + 1) (datumFourierCoeff (u t)) at h
  linarith

/-- Explicit algebraic reconstruction step. The unit error premise is to
be discharged by the differential bootstrap; this theorem does not supply it. -/
theorem eventual_canonical_slab_bound_of_error_and_reference
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (u : Velocity) (T K : ℝ)
    (herror : ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T,
      coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n t) ≤ 1)
    (hreference : ∀ n t, t ∈ Icc (0 : ℝ) T →
      coefficientDissipation (n + 1) (datumFourierCoeff (u t)) ≤ K) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T,
      canonicalEnstrophy ν hν a n t ≤ 1 + K := by
  filter_upwards [herror] with n hn
  intro t ht
  exact (canonical_enstrophy_le_error_plus_reference ν hν a u n t).trans
    (add_le_add (hn t ht) (hreference n t ht))

end

end MethbokeAddon.EhrenfestObstruction
