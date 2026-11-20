import MethbokeAddon.FDSNR3.SchwartzPhase

/-!
# The actual infinitesimal phase generator

The real Schwartz field below is reconstructed from the literal compact
frequency spectrum `i ψ û`. Its reality, solenoidal constraint and nonzero
value are derived from that spectrum, for use at a signed time-cutoff crossing.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff FourierTransform SchwartzMap ComplexConjugate

namespace MethbokeAddon.FDSNR3

noncomputable section

def realSchwartzInverse (a : 𝓢(Vec, CVec)) : 𝓢(Vec, Vec) :=
  realifySchwartz (𝓕⁻ a)

theorem complexifySchwartz_realSchwartzInverse
    (a : 𝓢(Vec, CVec))
    (ha : ∀ ξ : Vec, ∀ i : Fin 3, a (-ξ) i = conj (a ξ i)) :
    complexifySchwartz (realSchwartzInverse a) = 𝓕⁻ a := by
  apply SchwartzMap.ext
  intro x
  exact inverse_fourier_real_of_hermitian a ha x

theorem fourierVelocity_realSchwartzInverse
    (a : 𝓢(Vec, CVec))
    (ha : ∀ ξ : Vec, ∀ i : Fin 3, a (-ξ) i = conj (a ξ i)) (ξ : Vec) :
    fourierVelocity (realSchwartzInverse a) ξ = a ξ := by
  rw [fourierVelocity_eq_schwartz, complexifySchwartz_realSchwartzInverse a ha,
    schwartz_fourier_fourierInv]

theorem realSchwartzInverse_divergence_free
    (a : 𝓢(Vec, CVec))
    (ha : ∀ ξ : Vec, ∀ i : Fin 3, a (-ξ) i = conj (a ξ i))
    (hd : ∀ ξ : Vec, frequencyDot ξ (a ξ) = 0) :
    ∀ x : Vec, divergence (realSchwartzInverse a : Field) x = 0 := by
  apply divergence_free_of_fourierVelocity
  intro ξ
  change frequencyDot ξ (fourierVelocity (realSchwartzInverse a) ξ) = 0
  rw [fourierVelocity_realSchwartzInverse a ha]
  exact hd ξ

theorem realSchwartzInverse_ne_zero
    (a : 𝓢(Vec, CVec))
    (ha : ∀ ξ : Vec, ∀ i : Fin 3, a (-ξ) i = conj (a ξ i))
    {ξ : Vec} (hξ : a ξ ≠ 0) : realSchwartzInverse a ≠ 0 := by
  intro hz
  have h := fourierVelocity_realSchwartzInverse a ha ξ
  rw [hz] at h
  have hzero : fourierVelocity (0 : 𝓢(Vec, Vec)) ξ = 0 := by
    change 𝓕 (0 : Vec → CVec) ξ = 0
    simp
  exact hξ (h.symm.trans hzero)

/-- A genuine compactly supported scalar Schwartz multiplier. -/
def generatorMultiplier (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) : 𝓢(Vec, ℂ) :=
  (Complex.I : ℂ) • SchwartzMap.postcompCLM Complex.ofRealCLM (hc.toSchwartzMap hψ)

@[simp] theorem generatorMultiplier_apply (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (ξ : Vec) :
    generatorMultiplier ψ hψ hc ξ = Complex.I * (ψ ξ : ℂ) := rfl

def generatorSpectrum (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (f : 𝓢(Vec, Vec)) : 𝓢(Vec, CVec) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℂ ℂ).flip
    (generatorMultiplier ψ hψ hc).hasTemperateGrowth (𝓕 (complexifySchwartz f))

@[simp] theorem generatorSpectrum_apply (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (f : 𝓢(Vec, Vec)) (ξ : Vec) :
    generatorSpectrum ψ hψ hc f ξ =
      (Complex.I * (ψ ξ : ℂ)) • fourierVelocity f ξ := rfl

theorem generatorSpectrum_hermitian (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (f : 𝓢(Vec, Vec)) (ξ : Vec) (i : Fin 3) :
    generatorSpectrum ψ hψ hc f (-ξ) i =
      conj (generatorSpectrum ψ hψ hc f ξ i) := by
  change (Complex.I * (ψ (-ξ) : ℂ)) * fourierVelocity f (-ξ) i =
    conj ((Complex.I * (ψ ξ : ℂ)) * fourierVelocity f ξ i)
  rw [ho, fourierVelocity_conjugacy]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

theorem generatorSpectrum_tsupport (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (f : 𝓢(Vec, Vec)) : tsupport (generatorSpectrum ψ hψ hc f) ⊆ tsupport ψ := by
  apply closure_minimal ?_ isClosed_closure
  intro ξ hξ
  by_contra hn
  have hz : ψ ξ = 0 := image_eq_zero_of_notMem_tsupport hn
  apply hξ
  rw [generatorSpectrum_apply, hz, Complex.ofReal_zero, mul_zero, zero_smul]

def spectralGenerator (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (f : 𝓢(Vec, Vec)) : 𝓢(Vec, Vec) :=
  realSchwartzInverse (generatorSpectrum ψ hψ hc f)

theorem complexifySchwartz_spectralGenerator (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ) (f : 𝓢(Vec, Vec)) :
    complexifySchwartz (spectralGenerator ψ hψ hc f) =
      𝓕⁻ (generatorSpectrum ψ hψ hc f) :=
  complexifySchwartz_realSchwartzInverse _ (generatorSpectrum_hermitian ψ hψ hc ho f)

theorem fourierVelocity_spectralGenerator (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (f : 𝓢(Vec, Vec)) (ξ : Vec) :
    fourierVelocity (spectralGenerator ψ hψ hc f) ξ =
      (Complex.I * (ψ ξ : ℂ)) • fourierVelocity f ξ :=
  fourierVelocity_realSchwartzInverse _ (generatorSpectrum_hermitian ψ hψ hc ho f) ξ

theorem spectralGenerator_divergence_free (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (f : 𝓢(Vec, Vec)) (hf : ∀ x : Vec, divergence (f : Field) x = 0) :
    ∀ x : Vec, divergence (spectralGenerator ψ hψ hc f : Field) x = 0 := by
  apply realSchwartzInverse_divergence_free _ (generatorSpectrum_hermitian ψ hψ hc ho f)
  intro ξ
  rw [generatorSpectrum_apply, frequencyDot_smul]
  have hz : frequencyDot ξ (fourierVelocity f ξ) = 0 :=
    fourierVelocity_divergence_free f hf ξ
  rw [hz, mul_zero]

theorem spectralGenerator_ne_zero (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (f : 𝓢(Vec, Vec)) {ξ : Vec} {i : Fin 3}
    (hξ : ψ ξ ≠ 0) (hfξ : fourierVelocity f ξ i ≠ 0) :
    spectralGenerator ψ hψ hc f ≠ 0 := by
  apply realSchwartzInverse_ne_zero _ (generatorSpectrum_hermitian ψ hψ hc ho f)
    (ξ := ξ)
  intro hz
  have h := congrArg (fun z : CVec => z i) hz
  change (Complex.I * (ψ ξ : ℂ)) * fourierVelocity f ξ i = 0 at h
  exact (mul_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hξ)) hfξ) h

theorem fourierVelocity_spectralGenerator_at_active (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (f : 𝓢(Vec, Vec)) {ξ : Vec} (hξ : ψ ξ = 1) :
    fourierVelocity (spectralGenerator ψ hψ hc f) ξ =
      Complex.I • fourierVelocity f ξ := by
  rw [fourierVelocity_spectralGenerator ψ hψ hc ho, hξ, Complex.ofReal_one, mul_one]

end

end MethbokeAddon.FDSNR3
