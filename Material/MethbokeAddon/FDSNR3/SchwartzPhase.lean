import MethbokeAddon.FDSNR3.Fourier
import MethbokeAddon.FDSNR3.Phase
import MethbokeAddon.FDSNR3.Helical

/-!
# Actual Schwartz phase reconstruction at every regular slice

The scalar multiplier is admitted by a proved temperate-growth bound before
it acts on Schwartz space. The implementation uses bilinLeftCLM with that
proof, so there is no false-condition zero fallback. Its equality with
smulLeftCLM and its actual pointwise value are both proved.

Oddness yields a real inverse reconstruction. The physical Fourier, helical,
divergence, energy and dissipation identities all concern this same slice.
Joint parameter/time Schwartz regularity is a separate endpoint.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff FourierTransform SchwartzMap ComplexConjugate
open LineDeriv

namespace MethbokeAddon.FDSNR3

noncomputable section

def realifyCLM : CVec →L[ℝ] Vec :=
  ({ toFun := realify
     map_add' := by
       intro v w
       ext i
       simp [realify]
     map_smul' := by
       intro c v
       ext i
       simp [realify] } : CVec →ₗ[ℝ] Vec).toContinuousLinearMap

@[simp] theorem realifyCLM_apply (v : CVec) : realifyCLM v = realify v := rfl

def realifySchwartz (f : 𝓢(Vec, CVec)) : 𝓢(Vec, Vec) :=
  SchwartzMap.postcompCLM realifyCLM f

@[simp] theorem realifySchwartz_apply (f : 𝓢(Vec, CVec)) (x : Vec) :
    realifySchwartz f x = realify (f x) := rfl

@[simp] theorem realifySchwartz_complexifySchwartz (f : 𝓢(Vec, Vec)) :
    realifySchwartz (complexifySchwartz f) = f := by
  apply SchwartzMap.ext
  intro x
  exact realify_complexify (f x)

theorem contDiff_packetPhase_frequency
    (β : ℝ → ℝ) {ψ : Vec → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (lam t : ℝ) :
    ContDiff ℝ ∞ (packetPhase β ψ lam t) :=
  MethbokeAddon.FDSN.contDiff_phase.comp (contDiff_const.mul hψ)

theorem contDiff_packetPhaseIncrement_frequency
    (β : ℝ → ℝ) {ψ : Vec → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (lam t : ℝ) :
    ContDiff ℝ ∞ (packetPhaseIncrement β ψ lam t) :=
  (contDiff_packetPhase_frequency β hψ lam t).sub contDiff_const

theorem packetPhaseIncrement_hasTemperateGrowth
    (β : ℝ → ℝ) {ψ : Vec → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (lam t : ℝ) :
    Function.HasTemperateGrowth (packetPhaseIncrement β ψ lam t) := by
  exact ((hasCompactSupport_packetPhaseIncrement_frequency β hc lam t).toSchwartzMap
    (contDiff_packetPhaseIncrement_frequency β hψ lam t)).hasTemperateGrowth

theorem packetPhase_hasTemperateGrowth
    (β : ℝ → ℝ) {ψ : Vec → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (lam t : ℝ) :
    Function.HasTemperateGrowth (packetPhase β ψ lam t) := by
  have hinc := packetPhaseIncrement_hasTemperateGrowth β hψ hc lam t
  have hone : Function.HasTemperateGrowth (fun _ : Vec => (1 : ℂ)) := by fun_prop
  have heq : packetPhase β ψ lam t =
      packetPhaseIncrement β ψ lam t + (fun _ : Vec => (1 : ℂ)) := by
    funext ξ
    simp only [Pi.add_apply, packetPhaseIncrement, sub_add_cancel]
  rw [heq]
  exact hinc.add hone

/-- Multiplication by the proved admissible phase, with no fallback branch. -/
def packetMultiplierCLM
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (lam t : ℝ) :
    𝓢(Vec, CVec) →L[ℂ] 𝓢(Vec, CVec) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℂ ℂ).flip
    (packetPhase_hasTemperateGrowth β hψ hc lam t)

@[simp] theorem packetMultiplierCLM_apply
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)) (ξ : Vec) :
    packetMultiplierCLM β ψ hψ hc lam t f ξ =
      packetPhase β ψ lam t ξ • f ξ := rfl

theorem packetMultiplierCLM_eq_smulLeftCLM
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (lam t : ℝ) :
    packetMultiplierCLM β ψ hψ hc lam t =
      SchwartzMap.smulLeftCLM CVec (packetPhase β ψ lam t) := by
  ext f ξ
  rw [packetMultiplierCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (packetPhase_hasTemperateGrowth β hψ hc lam t)]

def phaseSpectrum
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)) : 𝓢(Vec, CVec) :=
  packetMultiplierCLM β ψ hψ hc lam t (𝓕 f)

@[simp] theorem phaseSpectrum_apply
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)) (ξ : Vec) :
    phaseSpectrum β ψ hψ hc lam t f ξ =
      packetPhase β ψ lam t ξ • 𝓕 f ξ := rfl

def complexPhaseSlice
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)) : 𝓢(Vec, CVec) :=
  𝓕⁻ (phaseSpectrum β ψ hψ hc lam t f)

theorem complexPhaseSlice_fourier
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)) :
    𝓕 (complexPhaseSlice β ψ hψ hc lam t f) =
      phaseSpectrum β ψ hψ hc lam t f :=
  schwartz_fourier_fourierInv _

def phaseSlice
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) : 𝓢(Vec, Vec) :=
  realifySchwartz (complexPhaseSlice β ψ hψ hc lam t (complexifySchwartz f))

theorem phaseSpectrum_hermitian
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) (ξ : Vec) (i : Fin 3) :
    phaseSpectrum β ψ hψ hc lam t (complexifySchwartz f) (-ξ) i =
      conj (phaseSpectrum β ψ hψ hc lam t (complexifySchwartz f) ξ i) := by
  rw [phaseSpectrum_apply, phaseSpectrum_apply]
  change packetPhase β ψ lam t (-ξ) * fourierVelocity f (-ξ) i =
    conj (packetPhase β ψ lam t ξ * fourierVelocity f ξ i)
  rw [packetPhase_neg β ho, fourierVelocity_conjugacy, map_mul]

theorem complexifySchwartz_phaseSlice
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) :
    complexifySchwartz (phaseSlice β ψ hψ hc lam t f) =
      complexPhaseSlice β ψ hψ hc lam t (complexifySchwartz f) := by
  apply SchwartzMap.ext
  intro x
  exact inverse_fourier_real_of_hermitian
    (phaseSpectrum β ψ hψ hc lam t (complexifySchwartz f))
    (phaseSpectrum_hermitian β ψ hψ hc ho lam t f) x

/-- The actual physical Fourier transform is precisely the prescribed phase. -/
theorem fourierVelocity_phaseSlice
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) (ξ : Vec) :
    fourierVelocity (phaseSlice β ψ hψ hc lam t f) ξ =
      packetPhase β ψ lam t ξ • fourierVelocity f ξ := by
  rw [fourierVelocity_eq_schwartz,
    complexifySchwartz_phaseSlice β ψ hψ hc ho,
    complexPhaseSlice_fourier, phaseSpectrum_apply] <;> rfl

theorem phaseSpectrum_eq_of_beta_zero
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam : ℝ) {t : ℝ} (hβ : β t = 0) (f : 𝓢(Vec, CVec)) :
    phaseSpectrum β ψ hψ hc lam t f = 𝓕 f := by
  apply SchwartzMap.ext
  intro ξ
  rw [phaseSpectrum_apply, packetPhase_eq_one_of_beta_zero ψ lam hβ, one_smul]

theorem phaseSlice_eq_of_beta_zero
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam : ℝ) {t : ℝ} (hβ : β t = 0) (f : 𝓢(Vec, Vec)) :
    phaseSlice β ψ hψ hc lam t f = f := by
  rw [phaseSlice, complexPhaseSlice,
    phaseSpectrum_eq_of_beta_zero β ψ hψ hc lam hβ,
    schwartz_fourierInv_fourier, realifySchwartz_complexifySchwartz]

theorem phaseSpectrum_zero_parameter
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (t : ℝ) (f : 𝓢(Vec, CVec)) :
    phaseSpectrum β ψ hψ hc 0 t f = 𝓕 f := by
  apply SchwartzMap.ext
  intro ξ
  rw [phaseSpectrum_apply, packetPhase_zero_parameter, one_smul]

theorem phaseSlice_zero_parameter
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (t : ℝ) (f : 𝓢(Vec, Vec)) :
    phaseSlice β ψ hψ hc 0 t f = f := by
  rw [phaseSlice, complexPhaseSlice, phaseSpectrum_zero_parameter,
    schwartz_fourierInv_fourier, realifySchwartz_complexifySchwartz]

theorem fourierVelocity_phaseSlice_eq_of_cutoff_zero
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) {ξ : Vec} (hξ : ψ ξ = 0) :
    fourierVelocity (phaseSlice β ψ hψ hc lam t f) ξ =
      fourierVelocity f ξ := by
  rw [fourierVelocity_phaseSlice β ψ hψ hc ho,
    packetPhase_eq_one_of_psi_zero β lam t hξ, one_smul]

theorem phaseSpectrum_difference_tsupport
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)) :
    tsupport (phaseSpectrum β ψ hψ hc lam t f - 𝓕 f) ⊆ tsupport ψ := by
  apply closure_minimal ?_ isClosed_closure
  intro ξ hξ
  by_contra hn
  have hz : ψ ξ = 0 := image_eq_zero_of_notMem_tsupport hn
  apply hξ
  change phaseSpectrum β ψ hψ hc lam t f ξ - 𝓕 f ξ = 0
  rw [phaseSpectrum_apply, packetPhase_eq_one_of_psi_zero β lam t hz,
    one_smul, sub_self]

theorem phaseSpectrum_difference_apply
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)) (ξ : Vec) :
    (phaseSpectrum β ψ hψ hc lam t f - 𝓕 f) ξ =
      packetPhaseIncrement β ψ lam t ξ • 𝓕 f ξ := by
  change phaseSpectrum β ψ hψ hc lam t f ξ - 𝓕 f ξ = _
  rw [phaseSpectrum_apply]
  simp only [packetPhaseIncrement, sub_smul, one_smul]

theorem complexPhaseSlice_sub
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, CVec)) :
    complexPhaseSlice β ψ hψ hc lam t f - f =
      𝓕⁻ (phaseSpectrum β ψ hψ hc lam t f - 𝓕 f) := by
  simp only [sub_eq_add_neg, FourierTransform.fourierInv_add,
    FourierTransform.fourierInv_neg, schwartz_fourierInv_fourier, complexPhaseSlice]

theorem phaseSlice_sub
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) :
    phaseSlice β ψ hψ hc lam t f - f =
      realifySchwartz (𝓕⁻
        (phaseSpectrum β ψ hψ hc lam t (complexifySchwartz f) -
          𝓕 (complexifySchwartz f))) := by
  rw [← complexPhaseSlice_sub]
  change realifySchwartz (complexPhaseSlice β ψ hψ hc lam t (complexifySchwartz f)) - f =
    (SchwartzMap.postcompCLM realifyCLM)
      (complexPhaseSlice β ψ hψ hc lam t (complexifySchwartz f) - complexifySchwartz f)
  rw [map_sub]
  change realifySchwartz (complexPhaseSlice β ψ hψ hc lam t (complexifySchwartz f)) - f =
    realifySchwartz (complexPhaseSlice β ψ hψ hc lam t (complexifySchwartz f)) -
      realifySchwartz (complexifySchwartz f)
  rw [realifySchwartz_complexifySchwartz]

theorem phaseSlice_helicalPower
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) (ξ : Vec) (σ : Fin 2) :
    helicalPower σ (phaseSlice β ψ hψ hc lam t f) ξ = helicalPower σ f ξ := by
  apply helicalPower_eq_of_fourier_phase σ f
    (phaseSlice β ψ hψ hc lam t f) ξ (lam * β t * ψ ξ)
  exact fourierVelocity_phaseSlice β ψ hψ hc ho lam t f ξ

/-- The actual Fourier constraint implies the physical divergence equation. -/
theorem divergence_free_of_fourierVelocity
    (f : 𝓢(Vec, Vec))
    (hf : ∀ ξ : Vec, ∑ i : Fin 3, (ξ i : ℂ) * fourierVelocity f ξ i = 0) :
    ∀ x : Vec, divergence (f : Field) x = 0 := by
  have hF : 𝓕 (schwartzDivergence (complexifySchwartz f)) = 0 := by
    apply SchwartzMap.ext
    intro ξ
    rw [fourier_schwartzDivergence]
    change (2 * (Real.pi : ℂ) * Complex.I) *
      (∑ i : Fin 3, (ξ i : ℂ) * fourierVelocity f ξ i) = 0
    rw [hf ξ, mul_zero]
  have hz : schwartzDivergence (complexifySchwartz f) = 0 := by
    have h := congrArg (𝓕⁻ : 𝓢(Vec, ℂ) → 𝓢(Vec, ℂ)) hF
    simpa only [FourierTransform.fourierInv_fourier_eq,
      FourierTransform.fourierInv_zero] using h
  intro x
  have h := congrArg (fun g : 𝓢(Vec, ℂ) => g x) hz
  rw [schwartzDivergence_complexify] at h
  exact Complex.ofReal_eq_zero.mp h

theorem phaseSlice_divergence_free
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec))
    (hf : ∀ x : Vec, divergence (f : Field) x = 0) :
    ∀ x : Vec, divergence (phaseSlice β ψ hψ hc lam t f : Field) x = 0 := by
  apply divergence_free_of_fourierVelocity
  intro ξ
  change frequencyDot ξ (fourierVelocity (phaseSlice β ψ hψ hc lam t f) ξ) = 0
  rw [fourierVelocity_phaseSlice β ψ hψ hc ho, frequencyDot_smul]
  have hz : frequencyDot ξ (fourierVelocity f ξ) = 0 :=
    fourierVelocity_divergence_free f hf ξ
  rw [hz, mul_zero]

/-- Explicit integrability prevents a totalized-integral interpretation. -/
theorem schwartz_integrable_norm_sq (f : 𝓢(Vec, Vec)) :
    Integrable (fun x : Vec => ‖f x‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).mp (f.memLp 2)

theorem physical_energy_eq_of_fourier_norm
    (f g : 𝓢(Vec, Vec))
    (h : ∀ ξ : Vec, ‖fourierVelocity g ξ‖ = ‖fourierVelocity f ξ‖) :
    (∫ x : Vec, ‖g x‖ ^ 2) = ∫ x : Vec, ‖f x‖ ^ 2 := by
  rw [← physical_plancherel g, ← physical_plancherel f]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [h ξ]

theorem phaseSlice_energy
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) :
    (∫ x : Vec, ‖phaseSlice β ψ hψ hc lam t f x‖ ^ 2) =
      ∫ x : Vec, ‖f x‖ ^ 2 := by
  apply physical_energy_eq_of_fourier_norm f
  intro ξ
  rw [fourierVelocity_phaseSlice β ψ hψ hc ho, norm_smul, norm_packetPhase, one_mul]

theorem complexifySchwartz_lineDeriv (f : 𝓢(Vec, Vec)) (m : Vec) :
    complexifySchwartz (∂_{m} f) = ∂_{m} (complexifySchwartz f) := by
  apply SchwartzMap.ext
  intro x
  simp only [complexifySchwartz_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change complexify (fderiv ℝ (f : Vec → Vec) x m) =
    fderiv ℝ (fun y => complexify (f y)) x m
  rw [fderiv_complexify f.differentiableAt] <;> rfl

theorem fourierVelocity_lineDeriv (f : 𝓢(Vec, Vec)) (m ξ : Vec) :
    fourierVelocity (∂_{m} f) ξ =
      (2 * (Real.pi : ℂ) * Complex.I) •
        ((inner ℝ ξ m) • fourierVelocity f ξ) := by
  rw [fourierVelocity_eq_schwartz, complexifySchwartz_lineDeriv]
  simpa only [SchwartzMap.fourier_coe, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    fourierVelocity_eq_schwartz] using
      fourier_directionalDerivative (complexifySchwartz f) m ξ

theorem phaseSlice_directional_energy
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) (m : Vec) :
    (∫ x : Vec, ‖(∂_{m} (phaseSlice β ψ hψ hc lam t f)) x‖ ^ 2) =
      ∫ x : Vec, ‖(∂_{m} f) x‖ ^ 2 := by
  apply physical_energy_eq_of_fourier_norm (∂_{m} f)
  intro ξ
  rw [fourierVelocity_lineDeriv, fourierVelocity_lineDeriv,
    fourierVelocity_phaseSlice β ψ hψ hc ho]
  simp only [norm_smul, norm_packetPhase, one_mul]

theorem schwartz_gradientSquare_integrable (f : 𝓢(Vec, Vec)) :
    Integrable (gradientSquare (f : Field)) volume := by
  simpa only [gradientSquare, coordinateDerivative,
    SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      (integrable_finsetSum Finset.univ
        (fun i _ => schwartz_integrable_norm_sq (∂_{unitVector i} f)))

theorem dissipation_eq_sum_directional_energy (f : 𝓢(Vec, Vec)) :
    dissipation (f : Field) =
      ∑ i : Fin 3, ∫ x : Vec, ‖(∂_{unitVector i} f) x‖ ^ 2 := by
  simpa only [dissipation, gradientSquare, coordinateDerivative,
    SchwartzMap.lineDerivOp_apply_eq_fderiv] using
      (integral_finsetSum Finset.univ
        (fun i _ => schwartz_integrable_norm_sq (∂_{unitVector i} f)))

theorem phaseSlice_dissipation
    (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (f : 𝓢(Vec, Vec)) :
    dissipation (phaseSlice β ψ hψ hc lam t f : Field) = dissipation (f : Field) := by
  rw [dissipation_eq_sum_directional_energy, dissipation_eq_sum_directional_energy]
  apply Finset.sum_congr rfl
  intro i _
  exact phaseSlice_directional_energy β ψ hψ hc ho lam t f (unitVector i)

end

end MethbokeAddon.FDSNR3

