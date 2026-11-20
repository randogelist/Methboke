import FDSNR3SpectralGenerator.Endpoint

set_option pp.universes true
set_option pp.fullNames true

set_option autoImplicit false

noncomputable section
open Set MeasureTheory SingularClosure MethbokeAddon.FDSNR3
open scoped BigOperators ContDiff FourierTransform SchwartzMap ComplexConjugate

example (a : 𝓢(Vec, CVec)) :
    realSchwartzInverse a = realifySchwartz (𝓕⁻ a) := rfl

example (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    generatorMultiplier ψ hψ hc =
      (Complex.I : ℂ) • SchwartzMap.postcompCLM Complex.ofRealCLM (hc.toSchwartzMap hψ) := rfl

example (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (f : 𝓢(Vec, Vec)) :
    generatorSpectrum ψ hψ hc f =
      SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℂ ℂ).flip
        (generatorMultiplier ψ hψ hc).hasTemperateGrowth (𝓕 (complexifySchwartz f)) := rfl

example (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (f : 𝓢(Vec, Vec)) :
    spectralGenerator ψ hψ hc f = realSchwartzInverse (generatorSpectrum ψ hψ hc f) := rfl

example : ∀ (a : 𝓢(Vec, CVec))
    (ha : ∀ ξ : Vec, ∀ i : Fin 3, a (-ξ) i = conj (a ξ i)),
    complexifySchwartz (realSchwartzInverse a) = 𝓕⁻ a :=
  @complexifySchwartz_realSchwartzInverse

example : ∀ (a : 𝓢(Vec, CVec))
    (ha : ∀ ξ : Vec, ∀ i : Fin 3, a (-ξ) i = conj (a ξ i)) (ξ : Vec),
    fourierVelocity (realSchwartzInverse a) ξ = a ξ :=
  @fourierVelocity_realSchwartzInverse

example : ∀ (a : 𝓢(Vec, CVec))
    (ha : ∀ ξ : Vec, ∀ i : Fin 3, a (-ξ) i = conj (a ξ i))
    (hd : ∀ ξ : Vec, frequencyDot ξ (a ξ) = 0),
    ∀ x : Vec, divergence (realSchwartzInverse a : Field) x = 0 :=
  @realSchwartzInverse_divergence_free

example : ∀ (a : 𝓢(Vec, CVec))
    (ha : ∀ ξ : Vec, ∀ i : Fin 3, a (-ξ) i = conj (a ξ i))
    {ξ : Vec} (hξ : a ξ ≠ 0),
    realSchwartzInverse a ≠ 0 :=
  @realSchwartzInverse_ne_zero

example : ∀ (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (ξ : Vec),
    generatorMultiplier ψ hψ hc ξ = Complex.I * (ψ ξ : ℂ) :=
  @generatorMultiplier_apply

example : ∀ (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (f : 𝓢(Vec, Vec)) (ξ : Vec),
    generatorSpectrum ψ hψ hc f ξ =
      (Complex.I * (ψ ξ : ℂ)) • fourierVelocity f ξ :=
  @generatorSpectrum_apply

example : ∀ (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (f : 𝓢(Vec, Vec)) (ξ : Vec) (i : Fin 3),
    generatorSpectrum ψ hψ hc f (-ξ) i =
      conj (generatorSpectrum ψ hψ hc f ξ i) :=
  @generatorSpectrum_hermitian

example : ∀ (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (f : 𝓢(Vec, Vec)),
    tsupport (generatorSpectrum ψ hψ hc f) ⊆ tsupport ψ :=
  @generatorSpectrum_tsupport

example : ∀ (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ) (f : 𝓢(Vec, Vec)),
    complexifySchwartz (spectralGenerator ψ hψ hc f) =
      𝓕⁻ (generatorSpectrum ψ hψ hc f) :=
  @complexifySchwartz_spectralGenerator

example : ∀ (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (f : 𝓢(Vec, Vec)) (ξ : Vec),
    fourierVelocity (spectralGenerator ψ hψ hc f) ξ =
      (Complex.I * (ψ ξ : ℂ)) • fourierVelocity f ξ :=
  @fourierVelocity_spectralGenerator

example : ∀ (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (f : 𝓢(Vec, Vec)) (hf : ∀ x : Vec, divergence (f : Field) x = 0),
    ∀ x : Vec, divergence (spectralGenerator ψ hψ hc f : Field) x = 0 :=
  @spectralGenerator_divergence_free

example : ∀ (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (f : 𝓢(Vec, Vec)) {ξ : Vec} {i : Fin 3}
    (hξ : ψ ξ ≠ 0) (hfξ : fourierVelocity f ξ i ≠ 0),
    spectralGenerator ψ hψ hc f ≠ 0 :=
  @spectralGenerator_ne_zero

example : ∀ (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (f : 𝓢(Vec, Vec)) {ξ : Vec} (hξ : ψ ξ = 1),
    fourierVelocity (spectralGenerator ψ hψ hc f) ξ =
      Complex.I • fourierVelocity f ξ :=
  @fourierVelocity_spectralGenerator_at_active

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.realSchwartzInverse"
#check @MethbokeAddon.FDSNR3.realSchwartzInverse
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.realSchwartzInverse"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.realSchwartzInverse"
#print axioms MethbokeAddon.FDSNR3.realSchwartzInverse
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.realSchwartzInverse"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexifySchwartz_realSchwartzInverse"
#check @MethbokeAddon.FDSNR3.complexifySchwartz_realSchwartzInverse
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexifySchwartz_realSchwartzInverse"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexifySchwartz_realSchwartzInverse"
#print axioms MethbokeAddon.FDSNR3.complexifySchwartz_realSchwartzInverse
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexifySchwartz_realSchwartzInverse"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_realSchwartzInverse"
#check @MethbokeAddon.FDSNR3.fourierVelocity_realSchwartzInverse
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierVelocity_realSchwartzInverse"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_realSchwartzInverse"
#print axioms MethbokeAddon.FDSNR3.fourierVelocity_realSchwartzInverse
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierVelocity_realSchwartzInverse"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.realSchwartzInverse_divergence_free"
#check @MethbokeAddon.FDSNR3.realSchwartzInverse_divergence_free
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.realSchwartzInverse_divergence_free"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.realSchwartzInverse_divergence_free"
#print axioms MethbokeAddon.FDSNR3.realSchwartzInverse_divergence_free
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.realSchwartzInverse_divergence_free"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.realSchwartzInverse_ne_zero"
#check @MethbokeAddon.FDSNR3.realSchwartzInverse_ne_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.realSchwartzInverse_ne_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.realSchwartzInverse_ne_zero"
#print axioms MethbokeAddon.FDSNR3.realSchwartzInverse_ne_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.realSchwartzInverse_ne_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.generatorMultiplier"
#check @MethbokeAddon.FDSNR3.generatorMultiplier
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.generatorMultiplier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.generatorMultiplier"
#print axioms MethbokeAddon.FDSNR3.generatorMultiplier
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.generatorMultiplier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.generatorMultiplier_apply"
#check @MethbokeAddon.FDSNR3.generatorMultiplier_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.generatorMultiplier_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.generatorMultiplier_apply"
#print axioms MethbokeAddon.FDSNR3.generatorMultiplier_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.generatorMultiplier_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.generatorSpectrum"
#check @MethbokeAddon.FDSNR3.generatorSpectrum
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.generatorSpectrum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.generatorSpectrum"
#print axioms MethbokeAddon.FDSNR3.generatorSpectrum
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.generatorSpectrum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.generatorSpectrum_apply"
#check @MethbokeAddon.FDSNR3.generatorSpectrum_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.generatorSpectrum_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.generatorSpectrum_apply"
#print axioms MethbokeAddon.FDSNR3.generatorSpectrum_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.generatorSpectrum_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.generatorSpectrum_hermitian"
#check @MethbokeAddon.FDSNR3.generatorSpectrum_hermitian
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.generatorSpectrum_hermitian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.generatorSpectrum_hermitian"
#print axioms MethbokeAddon.FDSNR3.generatorSpectrum_hermitian
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.generatorSpectrum_hermitian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.generatorSpectrum_tsupport"
#check @MethbokeAddon.FDSNR3.generatorSpectrum_tsupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.generatorSpectrum_tsupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.generatorSpectrum_tsupport"
#print axioms MethbokeAddon.FDSNR3.generatorSpectrum_tsupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.generatorSpectrum_tsupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.spectralGenerator"
#check @MethbokeAddon.FDSNR3.spectralGenerator
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.spectralGenerator"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.spectralGenerator"
#print axioms MethbokeAddon.FDSNR3.spectralGenerator
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.spectralGenerator"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexifySchwartz_spectralGenerator"
#check @MethbokeAddon.FDSNR3.complexifySchwartz_spectralGenerator
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexifySchwartz_spectralGenerator"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexifySchwartz_spectralGenerator"
#print axioms MethbokeAddon.FDSNR3.complexifySchwartz_spectralGenerator
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexifySchwartz_spectralGenerator"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_spectralGenerator"
#check @MethbokeAddon.FDSNR3.fourierVelocity_spectralGenerator
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierVelocity_spectralGenerator"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_spectralGenerator"
#print axioms MethbokeAddon.FDSNR3.fourierVelocity_spectralGenerator
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierVelocity_spectralGenerator"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.spectralGenerator_divergence_free"
#check @MethbokeAddon.FDSNR3.spectralGenerator_divergence_free
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.spectralGenerator_divergence_free"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.spectralGenerator_divergence_free"
#print axioms MethbokeAddon.FDSNR3.spectralGenerator_divergence_free
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.spectralGenerator_divergence_free"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.spectralGenerator_ne_zero"
#check @MethbokeAddon.FDSNR3.spectralGenerator_ne_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.spectralGenerator_ne_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.spectralGenerator_ne_zero"
#print axioms MethbokeAddon.FDSNR3.spectralGenerator_ne_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.spectralGenerator_ne_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_spectralGenerator_at_active"
#check @MethbokeAddon.FDSNR3.fourierVelocity_spectralGenerator_at_active
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierVelocity_spectralGenerator_at_active"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_spectralGenerator_at_active"
#print axioms MethbokeAddon.FDSNR3.fourierVelocity_spectralGenerator_at_active
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierVelocity_spectralGenerator_at_active"

