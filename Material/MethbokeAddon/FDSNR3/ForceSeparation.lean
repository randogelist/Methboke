import MethbokeAddon.FDSNR3.SpectralGenerator
import MethbokeAddon.FDSN.ResidualLocality

/-!
# Physical force separation at a common zero of the correction

A solenoidal real Schwartz field is fixed by the literal whole-space Leray
operator. At a common zero slice of two velocity corrections, every spatial
residual term vanishes and their force difference is precisely their native
time-derivative difference. A nonzero phase-generator slope therefore
separates the projected forces at this single time.

The derivative hypotheses below are explicit analytic bridge obligations.
They are not part of the seed and do not assert the separation conclusion.
The actual inverse-Fourier family must discharge them before root assembly.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open MethbokeAddon.EhrenfestObstruction
open scoped BigOperators ContDiff FourierTransform SchwartzMap

namespace MethbokeAddon.FDSNR3

noncomputable section

/-- The actual Fourier-multiplier Leray projection fixes a real solenoidal
Schwartz field, including the totalized zero-frequency convention. -/
theorem physicalLeray_eq_of_divergence_free_schwartz
    (f : 𝓢(Vec, Vec)) (hf : ∀ x : Vec, divergence (f : Field) x = 0) :
    physicalLeray (f : Field) = (f : Field) := by
  have hsymbol : (fun ξ : Vec => transverseSymbol ξ (fourierVelocity f ξ)) =
      fourierVelocity f := by
    funext ξ
    exact transverseSymbol_of_frequencyDot_eq_zero ξ
      (fourierVelocity_divergence_free f hf ξ)
  funext x
  change realify (𝓕⁻ (fun ξ : Vec => transverseSymbol ξ (fourierVelocity f ξ)) x) =
    f x
  rw [hsymbol]
  exact physical_fourier_inversion f x

/-- A constant real scalar preserves the literal physical divergence
equation. This proof differentiates the actual Schwartz function. -/
theorem divergence_free_schwartz_const_smul
    (c : ℝ) (f : 𝓢(Vec, Vec))
    (hf : ∀ x : Vec, divergence (f : Field) x = 0) :
    ∀ x : Vec, divergence (c • f : 𝓢(Vec, Vec)) x = 0 := by
  intro x
  have hfd : fderiv ℝ (fun y : Vec => c • f y) x =
      c • fderiv ℝ (f : Field) x := by
    exact fderiv_fun_const_smul f.differentiableAt c
  calc
    divergence (c • f : 𝓢(Vec, Vec)) x =
        ∑ i : Fin 3, c * (fderiv ℝ (f : Field) x (unitVector i)) i := by
      change (∑ i : Fin 3, (fderiv ℝ (fun y : Vec => c • f y) x (unitVector i)) i) = _
      rw [hfd]
      simp only [ContinuousLinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul]
    _ = c * divergence (f : Field) x := by
      simp only [divergence, coordinateDerivative, Finset.mul_sum]
    _ = 0 := by rw [hf x, mul_zero]

theorem physicalLeray_const_smul_solenoidal_schwartz
    (c : ℝ) (f : 𝓢(Vec, Vec))
    (hf : ∀ x : Vec, divergence (f : Field) x = 0) :
    physicalLeray (c • (f : Field)) = c • (f : Field) :=
  physicalLeray_eq_of_divergence_free_schwartz (c • f)
    (divergence_free_schwartz_const_smul c f hf)

/-- Spatial vanishing at one complete slice cancels all spatial terms;
the time derivative is deliberately retained. -/
theorem residualForce_at_zero_slice
    (ν : ℝ) (U F h : Velocity) (t : ℝ) (hz : h t = 0) :
    MethbokeAddon.FDSN.residualForce ν U F h t = F t + timeDerivative h t := by
  funext x
  simp [MethbokeAddon.FDSN.residualForce, hz,
    MethbokeAddon.FDSN.native_laplacian_zero, physicalTransport, convection]

theorem residualForce_sub_at_common_zero
    (ν : ℝ) (U F h k : Velocity) (t : ℝ)
    (hh : h t = 0) (hk : k t = 0) :
    (MethbokeAddon.FDSN.residualForce ν U F h -
      MethbokeAddon.FDSN.residualForce ν U F k) t =
      timeDerivative h t - timeDerivative k t := by
  change MethbokeAddon.FDSN.residualForce ν U F h t -
      MethbokeAddon.FDSN.residualForce ν U F k t = _
  rw [residualForce_at_zero_slice ν U F h t hh,
    residualForce_at_zero_slice ν U F k t hk]
  abel

/-- The residual difference at a crossing is a concrete scalar multiple of
a real solenoidal Schwartz field, and its physical Leray image is identical. -/
theorem physicalLeray_residual_difference_at_crossing
    (ν : ℝ) (U F h k : Velocity) (t c : ℝ) (w : 𝓢(Vec, Vec))
    (hh : h t = 0) (hk : k t = 0)
    (hdt : timeDerivative h t - timeDerivative k t = c • (w : Field))
    (hw : ∀ x : Vec, divergence (w : Field) x = 0) :
    physicalLeray ((MethbokeAddon.FDSN.residualForce ν U F h -
      MethbokeAddon.FDSN.residualForce ν U F k) t) = c • (w : Field) := by
  rw [residualForce_sub_at_common_zero ν U F h k t hh hk, hdt]
  exact physicalLeray_const_smul_solenoidal_schwartz c w hw

theorem projected_residual_difference_ne_zero_at_crossing
    (ν : ℝ) (U F h k : Velocity) (t c : ℝ) (w : 𝓢(Vec, Vec))
    (hh : h t = 0) (hk : k t = 0)
    (hdt : timeDerivative h t - timeDerivative k t = c • (w : Field))
    (hwdiv : ∀ x : Vec, divergence (w : Field) x = 0)
    (hc : c ≠ 0) (hw : w ≠ 0) :
    ∃ x : Vec, physicalLeray ((MethbokeAddon.FDSN.residualForce ν U F h -
      MethbokeAddon.FDSN.residualForce ν U F k) t) x ≠ 0 := by
  have hwpoint : ∃ x : Vec, w x ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hw
    exact SchwartzMap.ext hn
  obtain ⟨x, hx⟩ := hwpoint
  refine ⟨x, ?_⟩
  rw [physicalLeray_residual_difference_at_crossing ν U F h k t c w hh hk hdt hwdiv]
  exact smul_ne_zero hc hx

/-- The common crossing proves the complete contract for every distinct
pair of parameters in the original symmetric interval. Only the native derivative formula
for the constructed correction remains as an analytic input. -/
theorem physicalProjectedForceSeparation_of_common_crossing
    (ν T ε tzero slope : ℝ) (U F : Velocity) (h : ℝ → Velocity)
    (w : 𝓢(Vec, Vec)) (htzero : tzero ∈ Ico (0 : ℝ) T)
    (hslope : slope ≠ 0) (hw : w ≠ 0)
    (hwdiv : ∀ x : Vec, divergence (w : Field) x = 0)
    (hzero : ∀ lam : ℝ, |lam| < ε → h lam tzero = 0)
    (hdt : ∀ lam : ℝ, |lam| < ε →
      timeDerivative (h lam) tzero = (lam * slope) • (w : Field)) :
    PhysicalProjectedForceSeparation T ε
      (fun lam => MethbokeAddon.FDSN.residualForce ν U F (h lam)) := by
  intro lam eta hlam heta hne
  refine ⟨tzero, htzero, ?_⟩
  have hdifference : timeDerivative (h lam) tzero - timeDerivative (h eta) tzero =
      ((lam - eta) * slope) • (w : Field) := by
    rw [hdt lam hlam, hdt eta heta, ← sub_smul]
    congr 1
    ring
  exact projected_residual_difference_ne_zero_at_crossing ν U F
    (h lam) (h eta) tzero ((lam - eta) * slope) w
    (hzero lam hlam) (hzero eta heta) hdifference hwdiv
    (mul_ne_zero (sub_ne_zero.mpr hne) hslope) hw

/-- The nonzero/divergence facts required at a crossing follow from the
literal compact-frequency generator and one active Fourier coefficient. -/
theorem projected_residual_generator_difference_ne_zero
    (ν : ℝ) (U F h k : Velocity) (t c : ℝ)
    (ψ : Vec → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (f : 𝓢(Vec, Vec)) (hf : ∀ x : Vec, divergence (f : Field) x = 0)
    {ξ : Vec} {i : Fin 3} (hψξ : ψ ξ ≠ 0) (hfξ : fourierVelocity f ξ i ≠ 0)
    (hh : h t = 0) (hk : k t = 0) (hc : c ≠ 0)
    (hdt : timeDerivative h t - timeDerivative k t =
      c • (spectralGenerator ψ hψ hcψ f : Field)) :
    ∃ x : Vec, physicalLeray ((MethbokeAddon.FDSN.residualForce ν U F h -
      MethbokeAddon.FDSN.residualForce ν U F k) t) x ≠ 0 :=
  projected_residual_difference_ne_zero_at_crossing ν U F h k t c
    (spectralGenerator ψ hψ hcψ f) hh hk hdt
    (spectralGenerator_divergence_free ψ hψ hcψ ho f hf) hc
    (spectralGenerator_ne_zero ψ hψ hcψ ho f hψξ hfξ)

end

end MethbokeAddon.FDSNR3

