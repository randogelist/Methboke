import MethbokeAddon.R3Ehrenfest.SharpCutoff
import MethbokeAddon.R3Ehrenfest.FourierL1L2
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Coherent smooth representatives and a fixed-cutoff Bernstein bound

The finite-measure frequency ball supplies an actual scalar L2 indicator.
Holder multiplication constructs the L1 Fourier data, and the native L1
inverse Fourier CLM produces a bounded continuous function. The L1/L2 bridge
identifies it with the actual sharp cutoff. Every polynomial moment is
integrable because the same frequency support is bounded, so the same
representative is smooth.

The real representative is a bounded real-linear map on the original
SpatialL2. Its explicit, nonsharp constant is allowed to depend on n. This
is a fixed-cutoff construction estimate and is not a uniform nonlinear
comparison estimate. Directional derivative coherence, nonlinear products,
and trajectories remain subsequent native interfaces.

Prepared source only; matching authorized cached external compilation and
named type/axiom evidence are required. No local Lean, Lake or kernel run.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform ContDiff BoundedContinuousFunction NNReal

namespace MethbokeAddon.R3Ehrenfest.SmoothRepresentative

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.RealFourier
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open MethbokeAddon.R3Ehrenfest.SharpCutoff
open MethbokeAddon.R3Ehrenfest.FourierL1L2

abbrev ComplexL1 := Lp ComplexVector 1 (volume : Measure Space)

private theorem cutoffBall_measure_ne_top (n : ℕ) :
    volume (Metric.closedBall (0 : Space) (cutoffRadius n)) ≠ ∞ :=
  measure_closedBall_lt_top.ne

/-- Actual scalar L2 indicator of the finite-measure cutoff ball. -/
def cutoffMaskL2 (n : ℕ) : Lp ℂ 2 (volume : Measure Space) :=
  indicatorConstLp 2 measurableSet_closedBall (cutoffBall_measure_ne_top n) (1 : ℂ)

theorem cutoffMaskL2_ae (n : ℕ) :
    (fun ξ : Space => cutoffMaskL2 n ξ) =ᵐ[volume]
      (fun ξ : Space => (cutoffValue n ξ : ℂ)) := by
  have h := indicatorConstLp_coeFn
    (p := (2 : ℝ≥0∞))
    (hs := (measurableSet_closedBall :
      MeasurableSet (Metric.closedBall (0 : Space) (cutoffRadius n))))
    (hμs := cutoffBall_measure_ne_top n) (c := (1 : ℂ))
  filter_upwards [h] with ξ hξ
  change cutoffMaskL2 n ξ = (cutoffValue n ξ : ℂ)
  rw [show cutoffMaskL2 n ξ =
    (Metric.closedBall (0 : Space) (cutoffRadius n)).indicator (fun _ => (1 : ℂ)) ξ
      from hξ]
  by_cases hξball : ‖ξ‖ ≤ cutoffRadius n <;>
    simp [cutoffValue, hξball, Metric.mem_closedBall, dist_zero_right]

theorem norm_cutoffMaskL2 (n : ℕ) :
    ‖cutoffMaskL2 n‖ =
      volume.real (Metric.closedBall (0 : Space) (cutoffRadius n)) ^ (1 / (2 : ℝ)) := by
  simpa [cutoffMaskL2] using
    (norm_indicatorConstLp (p := (2 : ℝ≥0∞))
      (hs := (measurableSet_closedBall :
        MeasurableSet (Metric.closedBall (0 : Space) (cutoffRadius n))))
      (hμs := cutoffBall_measure_ne_top n) (c := (1 : ℂ))
      (by norm_num) (by norm_num))

private def scalarVectorSmul : ℂ →L[ℂ] ComplexVector →L[ℂ] ComplexVector :=
  ContinuousLinearMap.lsmul ℂ ℂ

/-- Holder's actual L2 by L2 multiplication supplies L1 cutoff Fourier data. -/
def cutoffFrequencyL1CLM (n : ℕ) : ComplexL2 →L[ℂ] ComplexL1 :=
  scalarVectorSmul.holderL volume 2 2 1 (cutoffMaskL2 n)

theorem cutoffFrequencyL1_ae (n : ℕ) (f : ComplexL2) :
    (fun ξ : Space => cutoffFrequencyL1CLM n f ξ) =ᵐ[volume]
      (fun ξ : Space => (cutoffValue n ξ : ℂ) • f ξ) := by
  have h := scalarVectorSmul.coeFn_holder (r := (1 : ℝ≥0∞)) (cutoffMaskL2 n) f
  filter_upwards [h, cutoffMaskL2_ae n] with ξ hξ hm
  change cutoffFrequencyL1CLM n f ξ = (cutoffValue n ξ : ℂ) • f ξ
  change cutoffFrequencyL1CLM n f ξ = (cutoffMaskL2 n ξ) • f ξ at hξ
  rw [hξ, hm]

theorem norm_cutoffFrequencyL1_le (n : ℕ) (f : ComplexL2) :
    ‖cutoffFrequencyL1CLM n f‖ ≤
      ‖(ContinuousLinearMap.lsmul ℂ ℂ :
        ℂ →L[ℂ] ComplexVector →L[ℂ] ComplexVector)‖ * ‖cutoffMaskL2 n‖ * ‖f‖ :=
  scalarVectorSmul.norm_holder_apply_apply_le (r := (1 : ℝ≥0∞)) (cutoffMaskL2 n) f

/-- Finite frequency support proves L1 membership of the actual Fourier class. -/
theorem integrable_sharpCutoff_fourier (n : ℕ) (u : SpatialL2) :
    Integrable (fun ξ : Space =>
      (𝓕 (complexifyL2 (sharpCutoff n u)) : ComplexL2) ξ) volume := by
  apply (L1.integrable_coeFn
    (cutoffFrequencyL1CLM n (𝓕 (complexifyL2 u)))).congr
  exact (cutoffFrequencyL1_ae n (𝓕 (complexifyL2 u))).trans
    (sharpCutoff_fourier_ae n u).symm

/-- The same bounded frequency support proves every polynomial L1 moment. -/
theorem integrable_sharpCutoff_fourier_moment
    (n : ℕ) (u : SpatialL2) (k : ℕ) :
    Integrable (fun ξ : Space => ‖ξ‖ ^ k *
      ‖(𝓕 (complexifyL2 (sharpCutoff n u)) : ComplexL2) ξ‖) volume := by
  have hf := integrable_sharpCutoff_fourier n u
  apply (hf.norm.const_mul ((cutoffRadius n) ^ k)).mono'
  · exact (continuous_norm.pow k).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable
        (𝓕 (complexifyL2 (sharpCutoff n u)) : ComplexL2)).norm
  · filter_upwards [sharpCutoff_fourier_outside n u] with ξ hout
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg ξ) k) (norm_nonneg _))]
    by_cases hξ : ‖ξ‖ ≤ cutoffRadius n
    · exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg ξ) hξ k) (norm_nonneg _)
    · rw [hout (lt_of_not_ge hξ), norm_zero, mul_zero, mul_zero]

/-- The actual complex bounded-continuous inverse after cutoff, as a CLM. -/
def sharpCutoffComplexRepresentativeCLM (n : ℕ) :
    ComplexL2 →L[ℂ] Space →ᵇ ComplexVector :=
  (Real.Lp.fourierTransformInvCLM Space ComplexVector).comp (cutoffFrequencyL1CLM n)

theorem complexRepresentative_eq_inverseL1 (n : ℕ) (u : SpatialL2) :
    sharpCutoffComplexRepresentativeCLM n (𝓕 (complexifyL2 u)) =
      inverseL1Representative (𝓕 (complexifyL2 (sharpCutoff n u)))
        (integrable_sharpCutoff_fourier n u) := by
  change Real.Lp.fourierTransformInv _ = Real.Lp.fourierTransformInv _
  congr 1
  apply Lp.ext
  filter_upwards [cutoffFrequencyL1_ae n (𝓕 (complexifyL2 u)),
    sharpCutoff_fourier_ae n u,
    (integrable_sharpCutoff_fourier n u).memLp_one.coeFn_toLp] with ξ h1 h2 h3
  exact h1.trans (h2.symm.trans h3.symm)

/-- A coherent actual smooth representative is built as a bounded real-linear
map; no representative, derivative, or regularity port is supplied. -/
def sharpCutoffRepresentativeCLM (n : ℕ) : SpatialL2 →L[ℝ] Space →ᵇ Space :=
  (realPartVectorCLM.compLeftContinuousBounded Space).comp
    (((sharpCutoffComplexRepresentativeCLM n).restrictScalars ℝ).comp
      ((((Lp.fourierTransformₗᵢ Space ComplexVector).toLinearIsometry.toContinuousLinearMap)
        .restrictScalars ℝ).comp complexifyL2LI.toContinuousLinearMap))

@[simp] theorem sharpCutoffRepresentativeCLM_apply
    (n : ℕ) (u : SpatialL2) (x : Space) :
    sharpCutoffRepresentativeCLM n u x =
      realPartVectorCLM
        (sharpCutoffComplexRepresentativeCLM n (𝓕 (complexifyL2 u)) x) := rfl

/-- The actual smooth representative agrees with the original sharp cutoff a.e. -/
theorem sharpCutoffRepresentative_ae (n : ℕ) (u : SpatialL2) :
    (fun x : Space => sharpCutoffRepresentativeCLM n u x) =ᵐ[volume]
      (fun x : Space => sharpCutoff n u x) := by
  have h := inverseL1Representative_ae
    (𝓕 (complexifyL2 (sharpCutoff n u)) : ComplexL2)
    (integrable_sharpCutoff_fourier n u)
  rw [fourierInv_fourier_eq] at h
  have hreal := realPartL2_ae (complexifyL2 (sharpCutoff n u))
  rw [realPartL2_complexify] at hreal
  filter_upwards [h, hreal] with x hx hr
  rw [sharpCutoffRepresentativeCLM_apply, complexRepresentative_eq_inverseL1, hx]
  exact hr.symm

/-- Smoothness is a conclusion of all constructed Fourier moments. -/
theorem contDiff_sharpCutoffRepresentative (n : ℕ) (u : SpatialL2) :
    ContDiff ℝ ∞ (fun x : Space => sharpCutoffRepresentativeCLM n u x) := by
  have hc := contDiff_inverseL1Representative
    (𝓕 (complexifyL2 (sharpCutoff n u)) : ComplexL2)
    (integrable_sharpCutoff_fourier n u)
    (integrable_sharpCutoff_fourier_moment n u)
  have he : (fun x : Space => sharpCutoffRepresentativeCLM n u x) =
      realPartVectorCLM ∘
        (fun x : Space => inverseL1Representative
          (𝓕 (complexifyL2 (sharpCutoff n u)) : ComplexL2)
          (integrable_sharpCutoff_fourier n u) x) := by
    funext x
    rw [sharpCutoffRepresentativeCLM_apply, complexRepresentative_eq_inverseL1]
    rfl
  rw [he]
  exact realPartVectorCLM.contDiff.comp hc

/-- An explicit finite fixed-cutoff constant. The indicator norm equals the
square root of the frequency-ball volume. No uniformity in n is asserted. -/
def bernsteinConstant (n : ℕ) : ℝ :=
  ‖realPartVectorCLM‖ * ‖Real.Lp.fourierTransformInvCLM Space ComplexVector‖ *
    ‖(ContinuousLinearMap.lsmul ℂ ℂ :
      ℂ →L[ℂ] ComplexVector →L[ℂ] ComplexVector)‖ * ‖cutoffMaskL2 n‖

theorem bernsteinConstant_nonneg (n : ℕ) : 0 ≤ bernsteinConstant n := by
  unfold bernsteinConstant
  positivity

/-- A proved fixed-cutoff L2-to-L-infinity Bernstein estimate for the same
actual native representative. -/
theorem norm_sharpCutoffRepresentative_le (n : ℕ) (u : SpatialL2) :
    ‖sharpCutoffRepresentativeCLM n u‖ ≤ bernsteinConstant n * ‖u‖ := by
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (bernsteinConstant_nonneg n) (norm_nonneg u))).mpr
  intro x
  let f : ComplexL2 := 𝓕 (complexifyL2 u)
  have hfnorm : ‖f‖ = ‖u‖ := by
    dsimp [f]
    rw [Lp.norm_fourier_eq, complexifyL2_norm]
  have hcomplex :
      ‖sharpCutoffComplexRepresentativeCLM n f‖ ≤
        ‖Real.Lp.fourierTransformInvCLM Space ComplexVector‖ *
          (‖scalarVectorSmul‖ * ‖cutoffMaskL2 n‖ * ‖f‖) := by
    calc
      _ ≤ ‖Real.Lp.fourierTransformInvCLM Space ComplexVector‖ *
          ‖cutoffFrequencyL1CLM n f‖ :=
        (Real.Lp.fourierTransformInvCLM Space ComplexVector).le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_cutoffFrequencyL1_le n f)
        (norm_nonneg _)
  calc
    ‖sharpCutoffRepresentativeCLM n u x‖ =
        ‖realPartVectorCLM (sharpCutoffComplexRepresentativeCLM n f x)‖ := rfl
    _ ≤ ‖realPartVectorCLM‖ * ‖sharpCutoffComplexRepresentativeCLM n f x‖ :=
      realPartVectorCLM.le_opNorm _
    _ ≤ ‖realPartVectorCLM‖ * ‖sharpCutoffComplexRepresentativeCLM n f‖ :=
      mul_le_mul_of_nonneg_left
        ((sharpCutoffComplexRepresentativeCLM n f).norm_coe_le_norm x) (norm_nonneg _)
    _ ≤ ‖realPartVectorCLM‖ *
        (‖Real.Lp.fourierTransformInvCLM Space ComplexVector‖ *
          (‖scalarVectorSmul‖ * ‖cutoffMaskL2 n‖ * ‖f‖)) :=
      mul_le_mul_of_nonneg_left hcomplex (norm_nonneg _)
    _ = bernsteinConstant n * ‖u‖ := by
      rw [hfnorm]
      dsimp [bernsteinConstant, scalarVectorSmul]
      ring

theorem sharpCutoffRepresentative_pointwise_le
    (n : ℕ) (u : SpatialL2) (x : Space) :
    ‖sharpCutoffRepresentativeCLM n u x‖ ≤ bernsteinConstant n * ‖u‖ :=
  ((sharpCutoffRepresentativeCLM n u).norm_coe_le_norm x).trans
    (norm_sharpCutoffRepresentative_le n u)

end MethbokeAddon.R3Ehrenfest.SmoothRepresentative

