import MethbokeAddon.QuasiFeffermanA.Contracts
import MethbokeAddon.QuasiFeffermanA.FourierMultipliers
import QFALC005.Density

/-!
# First-derivative Fourier identification from physical compact tests

The native real compact-test weak derivative extends to all complex Schwartz
tests by real/imaginary decomposition and the proved compact-Schwartz density
theorem. Fourier compatibility and the accepted generic multiplier bridge
then give the literal almost-everywhere first-derivative identity.

Only velocity and first-derivative L2 fields occur. No Laplacian/H2 witness,
PDE evolution, spectral-norm identity or solution-construction premise is used.
The reverse physical/spectral H1 equivalence and the six-projector construction
remain separate endpoints. Prepared source requires matching authorized cached
external compiler, exact consumer types and named standard-only axiom evidence.
No local Lean, Lake, kernel or project runner was executed.
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
open QFA.Endpoints.Representation.CompactSchwartz

private theorem real_smul_complexVector (r : ℝ) (z : ComplexVector) :
    r • z = (r : ℂ) • z := by
  apply PiLp.ext
  intro j
  change r • z j = (r : ℂ) * z j
  exact Complex.real_smul

/-- The real chain rule commutes a Schwartz directional derivative with the
actual scalar real-to-complex embedding. -/
theorem lineDeriv_postcomp_ofReal (ψ : 𝓢(Space, ℝ)) (e : Space) :
    ∂_{e} (ψ.postcompCLM Complex.ofRealCLM) =
      (∂_{e} ψ).postcompCLM Complex.ofRealCLM := by
  apply SchwartzMap.ext
  intro x
  change fderiv ℝ (fun y : Space => Complex.ofRealCLM (ψ y)) x e =
    Complex.ofRealCLM (fderiv ℝ ψ x e)
  have h := (Complex.ofRealCLM.hasFDerivAt.comp x (ψ.hasFDerivAt x)).fderiv
  exact congrArg (fun L : Space →L[ℝ] ℂ => L e) h

private theorem weak_eq_on_complexified_real_schwartz
    {u du : ComplexL2} {e : Space}
    (hweak : RealTestWeakDirectionalDerivative u du e)
    (ψ : 𝓢(Space, ℝ)) (hcompact : HasCompactSupport (ψ : Space → ℝ)) :
    (du : 𝓢'(Space, ComplexVector)) (ψ.postcompCLM Complex.ofRealCLM) =
      (∂_{e} (u : 𝓢'(Space, ComplexVector)))
        (ψ.postcompCLM Complex.ofRealCLM) := by
  have htest := hweak ψ (ψ.smooth ⊤) hcompact
  have htest' : (∫ x : Space, ψ x • du x) =
      -(∫ x : Space, fderiv ℝ ψ x e • u x) := by
    simpa only [neg_neg] using congrArg Neg.neg htest.symm
  calc
    (du : 𝓢'(Space, ComplexVector)) (ψ.postcompCLM Complex.ofRealCLM) =
        ∫ x : Space, ψ x • du x := by
      rw [Lp.toTemperedDistribution_apply]
      apply integral_congr_ae
      filter_upwards with x
      exact (real_smul_complexVector (ψ x) (du x)).symm
    _ = -(∫ x : Space, fderiv ℝ ψ x e • u x) := htest'
    _ = (∂_{e} (u : 𝓢'(Space, ComplexVector)))
        (ψ.postcompCLM Complex.ofRealCLM) := by
      rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
        Lp.toTemperedDistribution_apply]
      apply congrArg Neg.neg
      apply integral_congr_ae
      filter_upwards with x
      rw [lineDeriv_postcomp_ofReal]
      change fderiv ℝ ψ x e • u x = ((fderiv ℝ ψ x e : ℝ) : ℂ) • u x
      exact real_smul_complexVector (fderiv ℝ ψ x e) (u x)
  all_goals rfl

/-- Every real compact-test weak directional derivative is the actual complex
tempered-distribution derivative. All compact Schwartz tests are used; the
density premise is discharged by the retained proved density theorem. -/
theorem temperedDerivative_of_realTestWeakDirectionalDerivative
    {u du : ComplexL2} {e : Space}
    (hweak : RealTestWeakDirectionalDerivative u du e) :
    (du : 𝓢'(Space, ComplexVector)) = ∂_{e} (u : 𝓢'(Space, ComplexVector)) := by
  apply tempered_eq_of_eq_on_compactSchwartz denseCompactSchwartzTests
  intro φ hφ
  change HasCompactSupport (φ : Space → ℂ) at hφ
  let φr : 𝓢(Space, ℝ) := φ.postcompCLM Complex.reCLM
  let φi : 𝓢(Space, ℝ) := φ.postcompCLM Complex.imCLM
  have hrcompact : HasCompactSupport (φr : Space → ℝ) :=
    hφ.comp_left (g := Complex.reCLM) (by rfl)
  have hicompact : HasCompactSupport (φi : Space → ℝ) :=
    hφ.comp_left (g := Complex.imCLM) (by rfl)
  have hr := weak_eq_on_complexified_real_schwartz hweak φr hrcompact
  have hi := weak_eq_on_complexified_real_schwartz hweak φi hicompact
  have hsplit : φ = φr.postcompCLM Complex.ofRealCLM +
      Complex.I • φi.postcompCLM Complex.ofRealCLM := by
    apply SchwartzMap.ext
    intro x
    change φ x = ((φ x).re : ℂ) + Complex.I * ((φ x).im : ℂ)
    rw [mul_comm Complex.I]
    exact (Complex.re_add_im (φ x)).symm
  rw [hsplit]
  simp only [map_add, map_smul, hr, hi]

/-- Complexify the actual native real weak derivative and identify its
tempered-distribution derivative without a Laplacian hypothesis. -/
theorem complexify_temperedDerivative_of_realTestWeakDirectionalDerivative
    {u du : RealL2} {e : Space}
    (hweak : RealTestWeakDirectionalDerivative u du e) :
    (complexifyL2 du : 𝓢'(Space, ComplexVector)) =
      ∂_{e} (complexifyL2 u : 𝓢'(Space, ComplexVector)) :=
  temperedDerivative_of_realTestWeakDirectionalDerivative
    (complexifyL2_weakDirectionalDerivative hweak)

/-- Fourier differentiation for one actual supplied L2 distributional first
derivative. No higher derivative is required. -/
theorem fourier_directionalDerivative_distribution
    {u du : ComplexL2} {e : Space}
    (hweak : (du : 𝓢'(Space, ComplexVector)) =
      ∂_{e} (u : 𝓢'(Space, ComplexVector))) :
    ((𝓕 du : ComplexL2) : 𝓢'(Space, ComplexVector)) =
      (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ComplexVector
          (fun ξ : Space => (inner ℝ ξ e : ℂ))
          ((𝓕 u : ComplexL2) : 𝓢'(Space, ComplexVector)) := by
  calc
    ((𝓕 du : ComplexL2) : 𝓢'(Space, ComplexVector)) =
        𝓕 (du : 𝓢'(Space, ComplexVector)) :=
      (Lp.fourier_toTemperedDistribution_eq du).symm
    _ = 𝓕 (∂_{e} (u : 𝓢'(Space, ComplexVector))) := by rw [hweak]
    _ = (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ComplexVector
          (fun ξ : Space => (inner ℝ ξ e : ℂ))
          (𝓕 (u : 𝓢'(Space, ComplexVector))) := by
      simpa using TemperedDistribution.fourier_lineDerivOp_eq
        (u : 𝓢'(Space, ComplexVector)) e
    _ = _ := by rw [Lp.fourier_toTemperedDistribution_eq u]

/-- The a.e. first-derivative Fourier identity from the actual L2 distribution
equation. The accepted generic multiplier theorem discharges identification
of representatives for the unbounded linear frequency coordinate. -/
theorem fourier_directionalDerivative_ae
    {u du : ComplexL2} {e : Space}
    (hweak : (du : 𝓢'(Space, ComplexVector)) =
      ∂_{e} (u : 𝓢'(Space, ComplexVector))) :
    (fun ξ : Space => (𝓕 du : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space => ((2 * Real.pi * Complex.I) *
        (inner ℝ ξ e : ℂ)) • (𝓕 u : ComplexL2) ξ) := by
  exact FourierMultipliers.ae_eq_of_const_smul_real_multiplier_distribution
    (𝓕 du : ComplexL2) (𝓕 u : ComplexL2) (2 * Real.pi * Complex.I)
    (fun ξ : Space => inner ℝ ξ e) (by fun_prop) (by fun_prop)
    (fourier_directionalDerivative_distribution hweak)

/-- Literal compact real tests suffice for the a.e. Fourier derivative
identity of supplied complex vector L2 fields. -/
theorem fourier_of_realTestWeakDirectionalDerivative
    {u du : ComplexL2} {e : Space}
    (hweak : RealTestWeakDirectionalDerivative u du e) :
    (fun ξ : Space => (𝓕 du : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space => ((2 * Real.pi * Complex.I) *
        (inner ℝ ξ e : ℂ)) • (𝓕 u : ComplexL2) ξ) :=
  fourier_directionalDerivative_ae
    (temperedDerivative_of_realTestWeakDirectionalDerivative hweak)

/-- Actual real physical compact-test derivatives give the corresponding
Fourier identities under the native isometric complexification. -/
theorem complexify_fourier_of_realTestWeakDirectionalDerivative
    {u du : RealL2} {e : Space}
    (hweak : RealTestWeakDirectionalDerivative u du e) :
    (fun ξ : Space => (𝓕 (complexifyL2 du) : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space => ((2 * Real.pi * Complex.I) *
        (inner ℝ ξ e : ℂ)) • (𝓕 (complexifyL2 u) : ComplexL2) ξ) :=
  fourier_directionalDerivative_ae
    (complexify_temperedDerivative_of_realTestWeakDirectionalDerivative hweak)

/-- All three native physical weak-gradient components satisfy the literal
Fourier first-derivative identity simultaneously almost everywhere. -/
theorem spatialWeakGradient_fourier_ae
    {u : SpatialL2} {G : Fin 3 → SpatialL2}
    (hweak : SpatialWeakGradient u G) :
    ∀ᵐ ξ : Space ∂volume, ∀ j : Fin 3,
      (𝓕 (complexifyL2 (G j)) : ComplexL2) ξ =
        ((2 * Real.pi * Complex.I) * (inner ℝ ξ (coordinateVector j) : ℂ)) •
          (𝓕 (complexifyL2 u) : ComplexL2) ξ := by
  exact ae_all_iff.mpr (fun j =>
    complexify_fourier_of_realTestWeakDirectionalDerivative (hweak j))

end MethbokeAddon.QuasiFeffermanA.H1Fourier
