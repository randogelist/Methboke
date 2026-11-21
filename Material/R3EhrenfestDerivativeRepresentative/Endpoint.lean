import MethbokeAddon.R3Ehrenfest.Bandlimited
import MethbokeAddon.R3Ehrenfest.SmoothRepresentative
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Tactic.Ring

/-!
# Classical derivatives of the actual cutoff representative

The inverse Fourier differentiation theorem is applied with the negative
inner-product bilinear form, so its derivative has the positive 2*pi*i*xi
symbol. The proved L2 symbol of each constructed cutoffDerivative then
identifies every classical coordinate derivative of the same representative.

Iteration yields all ordered classical coordinate derivatives and finite
fixed-n bounds. These estimates do not enter a cutoff-uniform comparison.
This endpoint requires matching authorized cached external compilation and
named type/axiom evidence. No local Lean, Lake or kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform ContDiff BoundedContinuousFunction

namespace MethbokeAddon.R3Ehrenfest.DerivativeRepresentative

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.RealFourier
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open MethbokeAddon.R3Ehrenfest.SharpCutoff
open MethbokeAddon.R3Ehrenfest.Bandlimited
open MethbokeAddon.R3Ehrenfest.FourierL1L2
open MethbokeAddon.R3Ehrenfest.SmoothRepresentative

private theorem real_smul_complexVector (r : ℝ) (z : ComplexVector) :
    r • z = (r : ℂ) • z := by
  apply PiLp.ext
  intro j
  change r • z j = (r : ℂ) * z j
  exact Complex.real_smul

private theorem inverse_integral_hasFDerivAt (f : ComplexL2)
    (hf : Integrable (fun ξ : Space => f ξ) volume)
    (h1 : Integrable (fun ξ : Space => ‖ξ‖ * ‖f ξ‖) volume) (x : Space) :
    HasFDerivAt (𝓕⁻ (fun ξ : Space => f ξ))
      ((𝓕⁻ (VectorFourier.fourierSMulRight (-innerSL ℝ)
        (fun ξ : Space => f ξ))) x) x :=
  VectorFourier.hasFDerivAt_fourierIntegral (-innerSL ℝ) hf h1 x

/-- The classical inverse-integral derivative has the positive imaginary
coordinate symbol, with no differentiated Lp representative. -/
theorem fourierInv_integral_fderiv_apply (f : ComplexL2)
    (hf : Integrable (fun ξ : Space => f ξ) volume)
    (h1 : Integrable (fun ξ : Space => ‖ξ‖ * ‖f ξ‖) volume)
    (x e : Space) :
    fderiv ℝ (𝓕⁻ (fun ξ : Space => f ξ)) x e =
      (𝓕⁻ (fun ξ : Space =>
        ((2 * Real.pi * Complex.I) * (inner ℝ ξ e : ℂ)) • f ξ)) x := by
  let d : Space → (Space →L[ℝ] ComplexVector) :=
    VectorFourier.fourierSMulRight (-innerSL ℝ) (fun ξ : Space => f ξ)
  have hd : Integrable d volume := by
    apply (h1.const_mul (2 * Real.pi * ‖(-innerSL ℝ :
      Space →L[ℝ] Space →L[ℝ] ℝ)‖)).mono'
    · exact hf.aestronglyMeasurable.fourierSMulRight
    · filter_upwards with ξ
      simpa only [d, mul_assoc] using
        VectorFourier.norm_fourierSMulRight_le (-innerSL ℝ)
          (fun ξ : Space => f ξ) ξ
  calc
    fderiv ℝ (𝓕⁻ (fun ξ : Space => f ξ)) x e = (𝓕⁻ d) x e := by
      rw [(inverse_integral_hasFDerivAt f hf h1 x).fderiv]
    _ = (𝓕⁻ (fun ξ : Space => d ξ e)) x := by
      simpa only [Real.fourierInv_eq_fourier_neg] using
        (Real.fourier_continuousLinearMap_apply
          (f := d) (a := e) (v := -x) hd)
    _ = _ := by
      apply Real.fourierInv_congr_ae
      filter_upwards with ξ
      change -(2 * Real.pi * Complex.I) • (-(inner ℝ ξ e)) • f ξ =
        ((2 * Real.pi * Complex.I) * (inner ℝ ξ e : ℂ)) • f ξ
      rw [real_smul_complexVector, smul_smul, Complex.ofReal_neg]
      congr 1
      ring

/-- Classical coordinate differentiation of the coherent real representative
is exactly the representative of the already constructed native L2 derivative. -/
theorem fderiv_sharpCutoffRepresentative_coordinate
    (n : ℕ) (u : SpatialL2) (j : Fin 3) (x : Space) :
    fderiv ℝ (fun y : Space => sharpCutoffRepresentativeCLM n u y) x
      (coordinateVector j) =
        sharpCutoffRepresentativeCLM n (cutoffDerivative n j u) x := by
  let f : ComplexL2 := 𝓕 (complexifyL2 (sharpCutoff n u))
  have hf : Integrable (fun ξ : Space => f ξ) volume :=
    integrable_sharpCutoff_fourier n u
  have h1 : Integrable (fun ξ : Space => ‖ξ‖ * ‖f ξ‖) volume := by
    simpa only [pow_one] using integrable_sharpCutoff_fourier_moment n u 1
  have he : (fun y : Space => sharpCutoffRepresentativeCLM n u y) =
      realPartVectorCLM ∘ (𝓕⁻ (fun ξ : Space => f ξ)) := by
    funext y
    rw [sharpCutoffRepresentativeCLM_apply, complexRepresentative_eq_inverseL1,
      inverseL1Representative_apply]
    rfl
  have hD := inverse_integral_hasFDerivAt f hf h1 x
  have hR := realPartVectorCLM.hasFDerivAt.comp x hD
  have hcoord := fourierInv_integral_fderiv_apply f hf h1 x (coordinateVector j)
  rw [hD.fderiv] at hcoord
  rw [he, hR.fderiv]
  change realPartVectorCLM
      (((𝓕⁻ (VectorFourier.fourierSMulRight (-innerSL ℝ)
        (fun ξ : Space => f ξ))) x) (coordinateVector j)) =
    sharpCutoffRepresentativeCLM n (cutoffDerivative n j u) x
  rw [hcoord, sharpCutoffRepresentativeCLM_apply,
    complexRepresentative_eq_inverseL1, inverseL1Representative_apply,
    sharpCutoff_cutoffDerivative]
  congr 1
  apply Real.fourierInv_congr_ae
  exact (cutoffDerivative_fourier_ae n j u).symm

/-- The exact equality uses the gradient in the existing PhysicalH2 graph. -/
theorem fderiv_sharpCutoffRepresentative_physicalH2Gradient
    (n : ℕ) (u : SpatialL2) (j : Fin 3) (x : Space) :
    fderiv ℝ (fun y : Space => sharpCutoffRepresentativeCLM n u y) x
      (coordinateVector j) =
        sharpCutoffRepresentativeCLM n (physicalH2Gradient j (sharpCutoffH2 n u)) x := by
  rw [sharpCutoffH2_gradient]
  exact fderiv_sharpCutoffRepresentative_coordinate n u j x

/-- An ordered word of the actual bounded L2 derivative operators. -/
def cutoffWordCLM (n : ℕ) : List (Fin 3) → SpatialL2 →L[ℝ] SpatialL2
  | [] => ContinuousLinearMap.id ℝ SpatialL2
  | j :: a => (cutoffDerivative n j).comp (cutoffWordCLM n a)

theorem norm_cutoffWordCLM_apply_le (n : ℕ) (a : List (Fin 3)) (u : SpatialL2) :
    ‖cutoffWordCLM n a u‖ ≤ (cutoffDerivativeBound n) ^ a.length * ‖u‖ := by
  induction a with
  | nil => simp [cutoffWordCLM]
  | cons j a ih =>
    change ‖cutoffDerivative n j (cutoffWordCLM n a u)‖ ≤
      (cutoffDerivativeBound n) ^ (a.length + 1) * ‖u‖
    calc
      _ ≤ cutoffDerivativeBound n * ‖cutoffWordCLM n a u‖ :=
        norm_cutoffDerivative_le n j _
      _ ≤ cutoffDerivativeBound n *
          ((cutoffDerivativeBound n) ^ a.length * ‖u‖) :=
        mul_le_mul_of_nonneg_left ih (cutoffDerivativeBound_pos n).le
      _ = _ := by rw [pow_succ]; ring

/-- Actual classical coordinate differentiation, iterated in a prescribed order. -/
def coordinateIterate : List (Fin 3) → (Space → Space) → Space → Space
  | [], v => v
  | j :: a, v => fun x => fderiv ℝ (coordinateIterate a v) x (coordinateVector j)

theorem coordinateIterate_sharpCutoffRepresentative
    (n : ℕ) (a : List (Fin 3)) (u : SpatialL2) (x : Space) :
    coordinateIterate a (fun y : Space => sharpCutoffRepresentativeCLM n u y) x =
      sharpCutoffRepresentativeCLM n (cutoffWordCLM n a u) x := by
  induction a generalizing x with
  | nil => rfl
  | cons j a ih =>
    have he : coordinateIterate a
        (fun y : Space => sharpCutoffRepresentativeCLM n u y) =
        (fun y : Space => sharpCutoffRepresentativeCLM n (cutoffWordCLM n a u) y) := by
      funext y
      exact ih y
    change fderiv ℝ
      (coordinateIterate a (fun y : Space => sharpCutoffRepresentativeCLM n u y)) x
        (coordinateVector j) = _
    rw [he]
    exact fderiv_sharpCutoffRepresentative_coordinate n (cutoffWordCLM n a u) j x

/-- All ordered classical coordinate derivatives have a finite fixed-n
Bernstein bound, for the same constructed representative. -/
theorem coordinateIterate_sharpCutoffRepresentative_bound
    (n : ℕ) (a : List (Fin 3)) (u : SpatialL2) (x : Space) :
    ‖coordinateIterate a (fun y : Space => sharpCutoffRepresentativeCLM n u y) x‖ ≤
      bernsteinConstant n * (cutoffDerivativeBound n) ^ a.length * ‖u‖ := by
  rw [coordinateIterate_sharpCutoffRepresentative]
  calc
    _ ≤ bernsteinConstant n * ‖cutoffWordCLM n a u‖ :=
      sharpCutoffRepresentative_pointwise_le n _ x
    _ ≤ bernsteinConstant n * ((cutoffDerivativeBound n) ^ a.length * ‖u‖) :=
      mul_le_mul_of_nonneg_left (norm_cutoffWordCLM_apply_le n a u)
        (bernsteinConstant_nonneg n)
    _ = _ := by ring

end MethbokeAddon.R3Ehrenfest.DerivativeRepresentative
