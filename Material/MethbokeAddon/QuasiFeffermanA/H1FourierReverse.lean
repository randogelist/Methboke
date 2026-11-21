import MethbokeAddon.QuasiFeffermanA.H1Fourier

/-!
# Reverse H1-only Fourier identification for actual physical weak derivatives

A supplied L2 representative of the Fourier first-derivative multiplier gives
an exact tempered-distribution identity. Fourier inversion and restriction to
compact real tests then give the actual native weak derivative. Injectivity of
native complexification reflects this identity to real vector fields.

The resulting directional and three-component equivalences require only the
supplied real L2 velocity and first derivatives. They have no Laplacian, H2,
NSE evolution or spectral norm premise. Construction of derivative witnesses
from weighted integrability alone and the six projections are later endpoints.

Prepared second-batch source; matching authorized external compiler, expected
types and named axiom evidence are required. No local Lean execution is used.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap LineDeriv FourierTransform

namespace MethbokeAddon.QuasiFeffermanA.H1Fourier

open QFA.Endpoints.Agmon
open QFA.Endpoints.Representation

private theorem real_smul_complexVector_reverse (r : ℝ) (z : ComplexVector) :
    r • z = (r : ℂ) • z := by
  apply PiLp.ext
  intro j
  change r • z j = (r : ℂ) * z j
  exact Complex.real_smul

/-- A supplied actual L2 multiplier representative gives the corresponding
distribution identity. Temperate growth acts only on the Schwartz test. -/
theorem const_smul_real_multiplier_distribution_of_ae
    (q h : ComplexL2) (c : ℂ) (m : Space → ℝ)
    (hm : m.HasTemperateGrowth)
    (hae : (fun x : Space => q x) =ᵐ[volume]
      (fun x : Space => (c * (m x : ℂ)) • h x)) :
    (q : 𝓢'(Space, ComplexVector)) =
      c • TemperedDistribution.smulLeftCLM ComplexVector
        (fun x : Space => (m x : ℂ))
        (h : 𝓢'(Space, ComplexVector)) := by
  have hmC : (fun x : Space => (m x : ℂ)).HasTemperateGrowth := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasTemperateGrowth.comp hm)
  apply UniformConvergenceCLM.ext
  intro φ
  calc
    (q : 𝓢'(Space, ComplexVector)) φ = ∫ x : Space, φ x • q x :=
      Lp.toTemperedDistribution_apply q φ
    _ = ∫ x : Space, φ x • ((c * (m x : ℂ)) • h x) := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [hx]
    _ = c • ∫ x : Space, ((m x : ℂ) * φ x) • h x := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with x
      calc
        φ x • ((c * (m x : ℂ)) • h x) =
            (φ x * (c * (m x : ℂ))) • h x :=
          (mul_smul (φ x) (c * (m x : ℂ)) (h x)).symm
        _ = (c * ((m x : ℂ) * φ x)) • h x := by
          congr 1
          ring
        _ = c • (((m x : ℂ) * φ x) • h x) :=
          mul_smul c ((m x : ℂ) * φ x) (h x)
    _ = (c • TemperedDistribution.smulLeftCLM ComplexVector
        (fun x : Space => (m x : ℂ))
        (h : 𝓢'(Space, ComplexVector))) φ := by
      simp only [smul_apply, TemperedDistribution.smulLeftCLM_apply_apply,
        Lp.toTemperedDistribution_apply,
        SchwartzMap.smulLeftCLM_apply_apply hmC, smul_eq_mul]

/-- An a.e. Fourier first-derivative identity determines the distributional
derivative, by the actual Fourier inverse. No derivative witness is assumed. -/
theorem temperedDerivative_of_fourier_ae
    {u du : ComplexL2} {e : Space}
    (hae : (fun ξ : Space => (𝓕 du : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space => ((2 * Real.pi * Complex.I) *
        (inner ℝ ξ e : ℂ)) • (𝓕 u : ComplexL2) ξ)) :
    (du : 𝓢'(Space, ComplexVector)) = ∂_{e} (u : 𝓢'(Space, ComplexVector)) := by
  have hmult := const_smul_real_multiplier_distribution_of_ae
    (𝓕 du : ComplexL2) (𝓕 u : ComplexL2) (2 * Real.pi * Complex.I)
    (fun ξ : Space => inner ℝ ξ e) (by fun_prop) hae
  have hfourier : 𝓕 (du : 𝓢'(Space, ComplexVector)) =
      𝓕 (∂_{e} (u : 𝓢'(Space, ComplexVector))) := by
    calc
      𝓕 (du : 𝓢'(Space, ComplexVector)) =
          ((𝓕 du : ComplexL2) : 𝓢'(Space, ComplexVector)) :=
        Lp.fourier_toTemperedDistribution_eq du
      _ = (2 * Real.pi * Complex.I) •
          TemperedDistribution.smulLeftCLM ComplexVector
            (fun ξ : Space => (inner ℝ ξ e : ℂ))
            ((𝓕 u : ComplexL2) : 𝓢'(Space, ComplexVector)) := hmult
      _ = 𝓕 (∂_{e} (u : 𝓢'(Space, ComplexVector))) := by
        rw [← Lp.fourier_toTemperedDistribution_eq u]
        simpa using (TemperedDistribution.fourier_lineDerivOp_eq
          (u : 𝓢'(Space, ComplexVector)) e).symm
  have hinverse := congrArg
    (fun T : 𝓢'(Space, ComplexVector) => 𝓕⁻ T) hfourier
  simpa only [fourierInv_fourier_eq] using hinverse

/-- Restrict an actual distributional first derivative to all compact real
tests, with the literal native weak-derivative sign and scalar action. -/
theorem realTestWeakDirectionalDerivative_of_temperedDerivative
    {u du : ComplexL2} {e : Space}
    (hweak : (du : 𝓢'(Space, ComplexVector)) =
      ∂_{e} (u : 𝓢'(Space, ComplexVector))) :
    RealTestWeakDirectionalDerivative u du e := by
  intro ψ hψ hcompact
  let φ : 𝓢(Space, ℝ) := hcompact.toSchwartzMap hψ
  let test : 𝓢(Space, ℂ) := φ.postcompCLM Complex.ofRealCLM
  have hEval := congrArg (fun T : 𝓢'(Space, ComplexVector) => T test) hweak
  have hpair : (∫ x : Space, ψ x • du x) =
      -(∫ x : Space, fderiv ℝ ψ x e • u x) := by
    calc
      (∫ x : Space, ψ x • du x) =
          (du : 𝓢'(Space, ComplexVector)) test := by
        rw [Lp.toTemperedDistribution_apply]
        apply integral_congr_ae
        filter_upwards with x
        exact real_smul_complexVector_reverse (ψ x) (du x)
      _ = (∂_{e} (u : 𝓢'(Space, ComplexVector))) test := hEval
      _ = -(∫ x : Space, fderiv ℝ ψ x e • u x) := by
        rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
          Lp.toTemperedDistribution_apply]
        apply congrArg Neg.neg
        apply integral_congr_ae
        filter_upwards with x
        change (∂_{e} (φ.postcompCLM Complex.ofRealCLM)) x • u x =
          fderiv ℝ ψ x e • u x
        rw [lineDeriv_postcomp_ofReal]
        change ((fderiv ℝ ψ x e : ℝ) : ℂ) • u x = fderiv ℝ ψ x e • u x
        exact (real_smul_complexVector_reverse (fderiv ℝ ψ x e) (u x)).symm
  simpa only [neg_neg] using congrArg Neg.neg hpair.symm

/-- Injectivity of native real-to-complex embedding reflects the actual
compact-test weak derivative. Test integrability is proved before transport. -/
theorem realTestWeakDirectionalDerivative_of_complexify
    {u du : RealL2} {e : Space}
    (hweak : RealTestWeakDirectionalDerivative (complexifyL2 u) (complexifyL2 du) e) :
    RealTestWeakDirectionalDerivative u du e := by
  intro ψ hψ hcompact
  have hu : Integrable (fun x : Space => fderiv ℝ ψ x e • u x) volume :=
    integrable_compact_test_smul u
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hcompact.fderiv_apply ℝ e)
  have hdu : Integrable (fun x : Space => ψ x • du x) volume :=
    integrable_compact_test_smul du hψ.continuous hcompact
  have htest := hweak ψ hψ hcompact
  rw [integral_test_smul_complexifyL2 u (fun x => fderiv ℝ ψ x e) hu,
    integral_test_smul_complexifyL2 du ψ hdu] at htest
  apply complexifyVectorLI.injective
  change complexifyVectorCLM (∫ x : Space, fderiv ℝ ψ x e • u x) =
    complexifyVectorCLM (-(∫ x : Space, ψ x • du x))
  rw [map_neg]
  exact htest

/-- The reverse first-derivative Fourier implication for supplied complex L2
fields, with literal compact real tests. -/
theorem realTestWeakDirectionalDerivative_of_fourier_ae
    {u du : ComplexL2} {e : Space}
    (hae : (fun ξ : Space => (𝓕 du : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space => ((2 * Real.pi * Complex.I) *
        (inner ℝ ξ e : ℂ)) • (𝓕 u : ComplexL2) ξ)) :
    RealTestWeakDirectionalDerivative u du e :=
  realTestWeakDirectionalDerivative_of_temperedDerivative
    (temperedDerivative_of_fourier_ae hae)

/-- The reverse Fourier implication for actual supplied real L2 fields. -/
theorem realTestWeakDirectionalDerivative_of_complexify_fourier_ae
    {u du : RealL2} {e : Space}
    (hae : (fun ξ : Space => (𝓕 (complexifyL2 du) : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space => ((2 * Real.pi * Complex.I) *
        (inner ℝ ξ e : ℂ)) • (𝓕 (complexifyL2 u) : ComplexL2) ξ)) :
    RealTestWeakDirectionalDerivative u du e :=
  realTestWeakDirectionalDerivative_of_complexify
    (realTestWeakDirectionalDerivative_of_fourier_ae hae)

/-- Exact physical/Fourier characterization of a supplied real L2 first
derivative. This equivalence has no higher-derivative premise. -/
theorem realTestWeakDirectionalDerivative_iff_complexify_fourier_ae
    (u du : RealL2) (e : Space) :
    RealTestWeakDirectionalDerivative u du e ↔
      (fun ξ : Space => (𝓕 (complexifyL2 du) : ComplexL2) ξ) =ᵐ[volume]
        (fun ξ : Space => ((2 * Real.pi * Complex.I) *
          (inner ℝ ξ e : ℂ)) • (𝓕 (complexifyL2 u) : ComplexL2) ξ) :=
  ⟨complexify_fourier_of_realTestWeakDirectionalDerivative,
    realTestWeakDirectionalDerivative_of_complexify_fourier_ae⟩

/-- Exact simultaneous three-component characterization of the native physical
weak gradient. All velocity and derivative fields are real full-volume L2. -/
theorem spatialWeakGradient_iff_fourier_ae
    (u : SpatialL2) (G : Fin 3 → SpatialL2) :
    SpatialWeakGradient u G ↔
      ∀ᵐ ξ : Space ∂volume, ∀ j : Fin 3,
        (𝓕 (complexifyL2 (G j)) : ComplexL2) ξ =
          ((2 * Real.pi * Complex.I) * (inner ℝ ξ (coordinateVector j) : ℂ)) •
            (𝓕 (complexifyL2 u) : ComplexL2) ξ := by
  constructor
  · exact spatialWeakGradient_fourier_ae
  · intro h j
    apply realTestWeakDirectionalDerivative_of_complexify_fourier_ae
    exact ae_all_iff.mp h j

end MethbokeAddon.QuasiFeffermanA.H1Fourier
