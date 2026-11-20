import FDSNR3SchwartzPhase.Endpoint

set_option pp.universes true
set_option pp.fullNames true

set_option autoImplicit false

noncomputable section
open Set MeasureTheory SingularClosure MethbokeAddon.FDSNR3
open scoped BigOperators ContDiff FourierTransform SchwartzMap ComplexConjugate
open LineDeriv

example : ((realifyCLM : CVec →L[ℝ] Vec) : CVec → Vec) =
    (fun v => WithLp.toLp 2 (fun i : Fin 3 => (v i).re)) := rfl

example : (realifySchwartz : 𝓢(Vec, CVec) → 𝓢(Vec, Vec)) =
    (fun f => SchwartzMap.postcompCLM realifyCLM f) := rfl

example (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (lam t : ℝ) :
    packetMultiplierCLM β ψ hψ hc lam t =
      SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℂ ℂ).flip
        (packetPhase_hasTemperateGrowth β hψ hc lam t) := rfl

example (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)) :
    phaseSpectrum β ψ hψ hc lam t f =
      packetMultiplierCLM β ψ hψ hc lam t (𝓕 f) := rfl

example (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)) :
    complexPhaseSlice β ψ hψ hc lam t f =
      𝓕⁻ (phaseSpectrum β ψ hψ hc lam t f) := rfl

example (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) :
    phaseSlice β ψ hψ hc lam t f =
      realifySchwartz (complexPhaseSlice β ψ hψ hc lam t (complexifySchwartz f)) := rfl

example : ∀ (v : CVec),
    realifyCLM v = realify v :=
  @realifyCLM_apply

example : ∀ (f : 𝓢(Vec, CVec)) (x : Vec),
    realifySchwartz f x = realify (f x) :=
  @realifySchwartz_apply

example : ∀ (f : 𝓢(Vec, Vec)),
    realifySchwartz (complexifySchwartz f) = f :=
  @realifySchwartz_complexifySchwartz

example : ∀ (β : ℝ → ℝ) {ψ : Vec → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (lam t : ℝ),
    ContDiff ℝ ∞ (packetPhase β ψ lam t) :=
  @contDiff_packetPhase_frequency

example : ∀ (β : ℝ → ℝ) {ψ : Vec → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (lam t : ℝ),
    ContDiff ℝ ∞ (packetPhaseIncrement β ψ lam t) :=
  @contDiff_packetPhaseIncrement_frequency

example : ∀ (β : ℝ → ℝ) {ψ : Vec → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (lam t : ℝ),
    Function.HasTemperateGrowth (packetPhaseIncrement β ψ lam t) :=
  @packetPhaseIncrement_hasTemperateGrowth

example : ∀ (β : ℝ → ℝ) {ψ : Vec → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (lam t : ℝ),
    Function.HasTemperateGrowth (packetPhase β ψ lam t) :=
  @packetPhase_hasTemperateGrowth

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)) (ξ : Vec),
    packetMultiplierCLM β ψ hψ hc lam t f ξ =
      packetPhase β ψ lam t ξ • f ξ :=
  @packetMultiplierCLM_apply

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (lam t : ℝ),
    packetMultiplierCLM β ψ hψ hc lam t =
      SchwartzMap.smulLeftCLM CVec (packetPhase β ψ lam t) :=
  @packetMultiplierCLM_eq_smulLeftCLM

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)) (ξ : Vec),
    phaseSpectrum β ψ hψ hc lam t f ξ =
      packetPhase β ψ lam t ξ • 𝓕 f ξ :=
  @phaseSpectrum_apply

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)),
    𝓕 (complexPhaseSlice β ψ hψ hc lam t f) =
      phaseSpectrum β ψ hψ hc lam t f :=
  @complexPhaseSlice_fourier

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) (ξ : Vec) (i : Fin 3),
    phaseSpectrum β ψ hψ hc lam t (complexifySchwartz f) (-ξ) i =
      conj (phaseSpectrum β ψ hψ hc lam t (complexifySchwartz f) ξ i) :=
  @phaseSpectrum_hermitian

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)),
    complexifySchwartz (phaseSlice β ψ hψ hc lam t f) =
      complexPhaseSlice β ψ hψ hc lam t (complexifySchwartz f) :=
  @complexifySchwartz_phaseSlice

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) (ξ : Vec),
    fourierVelocity (phaseSlice β ψ hψ hc lam t f) ξ =
      packetPhase β ψ lam t ξ • fourierVelocity f ξ :=
  @fourierVelocity_phaseSlice

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam : ℝ) {t : ℝ} (hβ : β t = 0) (f : 𝓢(Vec, CVec)),
    phaseSpectrum β ψ hψ hc lam t f = 𝓕 f :=
  @phaseSpectrum_eq_of_beta_zero

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam : ℝ) {t : ℝ} (hβ : β t = 0) (f : 𝓢(Vec, Vec)),
    phaseSlice β ψ hψ hc lam t f = f :=
  @phaseSlice_eq_of_beta_zero

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (t : ℝ) (f : 𝓢(Vec, CVec)),
    phaseSpectrum β ψ hψ hc 0 t f = 𝓕 f :=
  @phaseSpectrum_zero_parameter

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (t : ℝ) (f : 𝓢(Vec, Vec)),
    phaseSlice β ψ hψ hc 0 t f = f :=
  @phaseSlice_zero_parameter

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) {ξ : Vec} (hξ : ψ ξ = 0),
    fourierVelocity (phaseSlice β ψ hψ hc lam t f) ξ =
      fourierVelocity f ξ :=
  @fourierVelocity_phaseSlice_eq_of_cutoff_zero

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)),
    tsupport (phaseSpectrum β ψ hψ hc lam t f - 𝓕 f) ⊆ tsupport ψ :=
  @phaseSpectrum_difference_tsupport

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)) (ξ : Vec),
    (phaseSpectrum β ψ hψ hc lam t f - 𝓕 f) ξ =
      packetPhaseIncrement β ψ lam t ξ • 𝓕 f ξ :=
  @phaseSpectrum_difference_apply

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)),
    complexPhaseSlice β ψ hψ hc lam t f - f =
      𝓕⁻ (phaseSpectrum β ψ hψ hc lam t f - 𝓕 f) :=
  @complexPhaseSlice_sub

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)),
    phaseSlice β ψ hψ hc lam t f - f =
      realifySchwartz (𝓕⁻
        (phaseSpectrum β ψ hψ hc lam t (complexifySchwartz f) -
          𝓕 (complexifySchwartz f))) :=
  @phaseSlice_sub

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) (ξ : Vec) (σ : Fin 2),
    helicalPower σ (phaseSlice β ψ hψ hc lam t f) ξ = helicalPower σ f ξ :=
  @phaseSlice_helicalPower

example : ∀ (f : 𝓢(Vec, Vec))
    (hf : ∀ ξ : Vec, ∑ i : Fin 3, (ξ i : ℂ) * fourierVelocity f ξ i = 0),
    ∀ x : Vec, divergence (f : Field) x = 0 :=
  @divergence_free_of_fourierVelocity

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec))
    (hf : ∀ x : Vec, divergence (f : Field) x = 0),
    ∀ x : Vec, divergence (phaseSlice β ψ hψ hc lam t f : Field) x = 0 :=
  @phaseSlice_divergence_free

example : ∀ (f : 𝓢(Vec, Vec)),
    Integrable (fun x : Vec => ‖f x‖ ^ 2) volume :=
  @schwartz_integrable_norm_sq

example : ∀ (f g : 𝓢(Vec, Vec))
    (h : ∀ ξ : Vec, ‖fourierVelocity g ξ‖ = ‖fourierVelocity f ξ‖),
    (∫ x : Vec, ‖g x‖ ^ 2) = ∫ x : Vec, ‖f x‖ ^ 2 :=
  @physical_energy_eq_of_fourier_norm

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)),
    (∫ x : Vec, ‖phaseSlice β ψ hψ hc lam t f x‖ ^ 2) =
      ∫ x : Vec, ‖f x‖ ^ 2 :=
  @phaseSlice_energy

example : ∀ (f : 𝓢(Vec, Vec)) (m : Vec),
    complexifySchwartz (∂_{m} f) = ∂_{m} (complexifySchwartz f) :=
  @complexifySchwartz_lineDeriv

example : ∀ (f : 𝓢(Vec, Vec)) (m ξ : Vec),
    fourierVelocity (∂_{m} f) ξ =
      (2 * (Real.pi : ℂ) * Complex.I) •
        ((inner ℝ ξ m) • fourierVelocity f ξ) :=
  @fourierVelocity_lineDeriv

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) (m : Vec),
    (∫ x : Vec, ‖(∂_{m} (phaseSlice β ψ hψ hc lam t f)) x‖ ^ 2) =
      ∫ x : Vec, ‖(∂_{m} f) x‖ ^ 2 :=
  @phaseSlice_directional_energy

example : ∀ (f : 𝓢(Vec, Vec)),
    Integrable (gradientSquare (f : Field)) volume :=
  @schwartz_gradientSquare_integrable

example : ∀ (f : 𝓢(Vec, Vec)),
    dissipation (f : Field) =
      ∑ i : Fin 3, ∫ x : Vec, ‖(∂_{unitVector i} f) x‖ ^ 2 :=
  @dissipation_eq_sum_directional_energy

example : ∀ (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)),
    dissipation (phaseSlice β ψ hψ hc lam t f : Field) = dissipation (f : Field) :=
  @phaseSlice_dissipation

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.realifyCLM"
#check @MethbokeAddon.FDSNR3.realifyCLM
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.realifyCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.realifyCLM"
#print axioms MethbokeAddon.FDSNR3.realifyCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.realifyCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.realifyCLM_apply"
#check @MethbokeAddon.FDSNR3.realifyCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.realifyCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.realifyCLM_apply"
#print axioms MethbokeAddon.FDSNR3.realifyCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.realifyCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.realifySchwartz"
#check @MethbokeAddon.FDSNR3.realifySchwartz
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.realifySchwartz"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.realifySchwartz"
#print axioms MethbokeAddon.FDSNR3.realifySchwartz
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.realifySchwartz"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.realifySchwartz_apply"
#check @MethbokeAddon.FDSNR3.realifySchwartz_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.realifySchwartz_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.realifySchwartz_apply"
#print axioms MethbokeAddon.FDSNR3.realifySchwartz_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.realifySchwartz_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.realifySchwartz_complexifySchwartz"
#check @MethbokeAddon.FDSNR3.realifySchwartz_complexifySchwartz
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.realifySchwartz_complexifySchwartz"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.realifySchwartz_complexifySchwartz"
#print axioms MethbokeAddon.FDSNR3.realifySchwartz_complexifySchwartz
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.realifySchwartz_complexifySchwartz"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.contDiff_packetPhase_frequency"
#check @MethbokeAddon.FDSNR3.contDiff_packetPhase_frequency
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.contDiff_packetPhase_frequency"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.contDiff_packetPhase_frequency"
#print axioms MethbokeAddon.FDSNR3.contDiff_packetPhase_frequency
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.contDiff_packetPhase_frequency"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.contDiff_packetPhaseIncrement_frequency"
#check @MethbokeAddon.FDSNR3.contDiff_packetPhaseIncrement_frequency
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.contDiff_packetPhaseIncrement_frequency"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.contDiff_packetPhaseIncrement_frequency"
#print axioms MethbokeAddon.FDSNR3.contDiff_packetPhaseIncrement_frequency
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.contDiff_packetPhaseIncrement_frequency"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetPhaseIncrement_hasTemperateGrowth"
#check @MethbokeAddon.FDSNR3.packetPhaseIncrement_hasTemperateGrowth
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetPhaseIncrement_hasTemperateGrowth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetPhaseIncrement_hasTemperateGrowth"
#print axioms MethbokeAddon.FDSNR3.packetPhaseIncrement_hasTemperateGrowth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetPhaseIncrement_hasTemperateGrowth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetPhase_hasTemperateGrowth"
#check @MethbokeAddon.FDSNR3.packetPhase_hasTemperateGrowth
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetPhase_hasTemperateGrowth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetPhase_hasTemperateGrowth"
#print axioms MethbokeAddon.FDSNR3.packetPhase_hasTemperateGrowth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetPhase_hasTemperateGrowth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetMultiplierCLM"
#check @MethbokeAddon.FDSNR3.packetMultiplierCLM
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetMultiplierCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetMultiplierCLM"
#print axioms MethbokeAddon.FDSNR3.packetMultiplierCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetMultiplierCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetMultiplierCLM_apply"
#check @MethbokeAddon.FDSNR3.packetMultiplierCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetMultiplierCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetMultiplierCLM_apply"
#print axioms MethbokeAddon.FDSNR3.packetMultiplierCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetMultiplierCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetMultiplierCLM_eq_smulLeftCLM"
#check @MethbokeAddon.FDSNR3.packetMultiplierCLM_eq_smulLeftCLM
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetMultiplierCLM_eq_smulLeftCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetMultiplierCLM_eq_smulLeftCLM"
#print axioms MethbokeAddon.FDSNR3.packetMultiplierCLM_eq_smulLeftCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetMultiplierCLM_eq_smulLeftCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSpectrum"
#check @MethbokeAddon.FDSNR3.phaseSpectrum
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSpectrum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSpectrum"
#print axioms MethbokeAddon.FDSNR3.phaseSpectrum
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSpectrum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSpectrum_apply"
#check @MethbokeAddon.FDSNR3.phaseSpectrum_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSpectrum_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSpectrum_apply"
#print axioms MethbokeAddon.FDSNR3.phaseSpectrum_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSpectrum_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexPhaseSlice"
#check @MethbokeAddon.FDSNR3.complexPhaseSlice
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexPhaseSlice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexPhaseSlice"
#print axioms MethbokeAddon.FDSNR3.complexPhaseSlice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexPhaseSlice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexPhaseSlice_fourier"
#check @MethbokeAddon.FDSNR3.complexPhaseSlice_fourier
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexPhaseSlice_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexPhaseSlice_fourier"
#print axioms MethbokeAddon.FDSNR3.complexPhaseSlice_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexPhaseSlice_fourier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSlice"
#check @MethbokeAddon.FDSNR3.phaseSlice
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSlice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSlice"
#print axioms MethbokeAddon.FDSNR3.phaseSlice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSlice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSpectrum_hermitian"
#check @MethbokeAddon.FDSNR3.phaseSpectrum_hermitian
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSpectrum_hermitian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSpectrum_hermitian"
#print axioms MethbokeAddon.FDSNR3.phaseSpectrum_hermitian
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSpectrum_hermitian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexifySchwartz_phaseSlice"
#check @MethbokeAddon.FDSNR3.complexifySchwartz_phaseSlice
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexifySchwartz_phaseSlice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexifySchwartz_phaseSlice"
#print axioms MethbokeAddon.FDSNR3.complexifySchwartz_phaseSlice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexifySchwartz_phaseSlice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_phaseSlice"
#check @MethbokeAddon.FDSNR3.fourierVelocity_phaseSlice
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierVelocity_phaseSlice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_phaseSlice"
#print axioms MethbokeAddon.FDSNR3.fourierVelocity_phaseSlice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierVelocity_phaseSlice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSpectrum_eq_of_beta_zero"
#check @MethbokeAddon.FDSNR3.phaseSpectrum_eq_of_beta_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSpectrum_eq_of_beta_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSpectrum_eq_of_beta_zero"
#print axioms MethbokeAddon.FDSNR3.phaseSpectrum_eq_of_beta_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSpectrum_eq_of_beta_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_eq_of_beta_zero"
#check @MethbokeAddon.FDSNR3.phaseSlice_eq_of_beta_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSlice_eq_of_beta_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_eq_of_beta_zero"
#print axioms MethbokeAddon.FDSNR3.phaseSlice_eq_of_beta_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSlice_eq_of_beta_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSpectrum_zero_parameter"
#check @MethbokeAddon.FDSNR3.phaseSpectrum_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSpectrum_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSpectrum_zero_parameter"
#print axioms MethbokeAddon.FDSNR3.phaseSpectrum_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSpectrum_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_zero_parameter"
#check @MethbokeAddon.FDSNR3.phaseSlice_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSlice_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_zero_parameter"
#print axioms MethbokeAddon.FDSNR3.phaseSlice_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSlice_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_phaseSlice_eq_of_cutoff_zero"
#check @MethbokeAddon.FDSNR3.fourierVelocity_phaseSlice_eq_of_cutoff_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierVelocity_phaseSlice_eq_of_cutoff_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_phaseSlice_eq_of_cutoff_zero"
#print axioms MethbokeAddon.FDSNR3.fourierVelocity_phaseSlice_eq_of_cutoff_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierVelocity_phaseSlice_eq_of_cutoff_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSpectrum_difference_tsupport"
#check @MethbokeAddon.FDSNR3.phaseSpectrum_difference_tsupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSpectrum_difference_tsupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSpectrum_difference_tsupport"
#print axioms MethbokeAddon.FDSNR3.phaseSpectrum_difference_tsupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSpectrum_difference_tsupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSpectrum_difference_apply"
#check @MethbokeAddon.FDSNR3.phaseSpectrum_difference_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSpectrum_difference_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSpectrum_difference_apply"
#print axioms MethbokeAddon.FDSNR3.phaseSpectrum_difference_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSpectrum_difference_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexPhaseSlice_sub"
#check @MethbokeAddon.FDSNR3.complexPhaseSlice_sub
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexPhaseSlice_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexPhaseSlice_sub"
#print axioms MethbokeAddon.FDSNR3.complexPhaseSlice_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexPhaseSlice_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_sub"
#check @MethbokeAddon.FDSNR3.phaseSlice_sub
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSlice_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_sub"
#print axioms MethbokeAddon.FDSNR3.phaseSlice_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSlice_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_helicalPower"
#check @MethbokeAddon.FDSNR3.phaseSlice_helicalPower
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSlice_helicalPower"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_helicalPower"
#print axioms MethbokeAddon.FDSNR3.phaseSlice_helicalPower
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSlice_helicalPower"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.divergence_free_of_fourierVelocity"
#check @MethbokeAddon.FDSNR3.divergence_free_of_fourierVelocity
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.divergence_free_of_fourierVelocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.divergence_free_of_fourierVelocity"
#print axioms MethbokeAddon.FDSNR3.divergence_free_of_fourierVelocity
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.divergence_free_of_fourierVelocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_divergence_free"
#check @MethbokeAddon.FDSNR3.phaseSlice_divergence_free
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSlice_divergence_free"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_divergence_free"
#print axioms MethbokeAddon.FDSNR3.phaseSlice_divergence_free
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSlice_divergence_free"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartz_integrable_norm_sq"
#check @MethbokeAddon.FDSNR3.schwartz_integrable_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartz_integrable_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartz_integrable_norm_sq"
#print axioms MethbokeAddon.FDSNR3.schwartz_integrable_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartz_integrable_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physical_energy_eq_of_fourier_norm"
#check @MethbokeAddon.FDSNR3.physical_energy_eq_of_fourier_norm
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physical_energy_eq_of_fourier_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physical_energy_eq_of_fourier_norm"
#print axioms MethbokeAddon.FDSNR3.physical_energy_eq_of_fourier_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physical_energy_eq_of_fourier_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_energy"
#check @MethbokeAddon.FDSNR3.phaseSlice_energy
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSlice_energy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_energy"
#print axioms MethbokeAddon.FDSNR3.phaseSlice_energy
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSlice_energy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexifySchwartz_lineDeriv"
#check @MethbokeAddon.FDSNR3.complexifySchwartz_lineDeriv
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexifySchwartz_lineDeriv"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexifySchwartz_lineDeriv"
#print axioms MethbokeAddon.FDSNR3.complexifySchwartz_lineDeriv
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexifySchwartz_lineDeriv"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_lineDeriv"
#check @MethbokeAddon.FDSNR3.fourierVelocity_lineDeriv
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierVelocity_lineDeriv"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_lineDeriv"
#print axioms MethbokeAddon.FDSNR3.fourierVelocity_lineDeriv
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierVelocity_lineDeriv"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_directional_energy"
#check @MethbokeAddon.FDSNR3.phaseSlice_directional_energy
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSlice_directional_energy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_directional_energy"
#print axioms MethbokeAddon.FDSNR3.phaseSlice_directional_energy
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSlice_directional_energy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartz_gradientSquare_integrable"
#check @MethbokeAddon.FDSNR3.schwartz_gradientSquare_integrable
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartz_gradientSquare_integrable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartz_gradientSquare_integrable"
#print axioms MethbokeAddon.FDSNR3.schwartz_gradientSquare_integrable
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartz_gradientSquare_integrable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.dissipation_eq_sum_directional_energy"
#check @MethbokeAddon.FDSNR3.dissipation_eq_sum_directional_energy
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.dissipation_eq_sum_directional_energy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.dissipation_eq_sum_directional_energy"
#print axioms MethbokeAddon.FDSNR3.dissipation_eq_sum_directional_energy
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.dissipation_eq_sum_directional_energy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_dissipation"
#check @MethbokeAddon.FDSNR3.phaseSlice_dissipation
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseSlice_dissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseSlice_dissipation"
#print axioms MethbokeAddon.FDSNR3.phaseSlice_dissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseSlice_dissipation"

