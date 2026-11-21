import R3EhrenfestSmoothRepresentative.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap ContDiff BoundedContinuousFunction

namespace R3EhrenfestSmoothRepresentative.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.RealFourier
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open MethbokeAddon.R3Ehrenfest.SharpCutoff
open MethbokeAddon.R3Ehrenfest.FourierL1L2
open MethbokeAddon.R3Ehrenfest.SmoothRepresentative

-- Native real and complex whole-space carriers and measure.
example : Space = EuclideanSpace ℝ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL1 = Lp (EuclideanSpace ℂ (Fin 3)) 1
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl

-- The actual finite-ball scalar L2 mask supplies Holder L1 data.
example (n : ℕ) : Lp ℂ 2 (volume : Measure Space) := cutoffMaskL2 n
example (n : ℕ) :
    (fun ξ : Space => cutoffMaskL2 n ξ) =ᵐ[volume]
      (fun ξ : Space => ((if ‖ξ‖ ≤ (n : ℝ) + 1 then 1 else 0 : ℝ) : ℂ)) :=
  cutoffMaskL2_ae n
example (n : ℕ) :
    ‖cutoffMaskL2 n‖ =
      volume.real (Metric.closedBall (0 : Space) ((n : ℝ) + 1)) ^ (1 / (2 : ℝ)) :=
  norm_cutoffMaskL2 n
example (n : ℕ) :
    ComplexL2 →L[ℂ] Lp ComplexVector 1 (volume : Measure Space) := cutoffFrequencyL1CLM n
example (n : ℕ) (f : ComplexL2) :
    (fun ξ : Space => cutoffFrequencyL1CLM n f ξ) =ᵐ[volume]
      (fun ξ : Space => (cutoffValue n ξ : ℂ) • f ξ) := cutoffFrequencyL1_ae n f
example (n : ℕ) (f : ComplexL2) :
    ‖cutoffFrequencyL1CLM n f‖ ≤
      ‖(ContinuousLinearMap.lsmul ℂ ℂ :
        ℂ →L[ℂ] ComplexVector →L[ℂ] ComplexVector)‖ * ‖cutoffMaskL2 n‖ * ‖f‖ :=
  norm_cutoffFrequencyL1_le n f

-- All L1 moments of the actual cutoff Fourier class are proved for arbitrary L2 data.
example (n : ℕ) (u : SpatialL2) :
    Integrable (fun ξ : Space =>
      (𝓕 (complexifyL2 (sharpCutoff n u)) : ComplexL2) ξ) volume :=
  integrable_sharpCutoff_fourier n u
example (n : ℕ) (u : SpatialL2) (k : ℕ) :
    Integrable (fun ξ : Space => ‖ξ‖ ^ k *
      ‖(𝓕 (complexifyL2 (sharpCutoff n u)) : ComplexL2) ξ‖) volume :=
  integrable_sharpCutoff_fourier_moment n u k

-- Actual bounded continuous maps, with the proved L1/L2 identification.
example (n : ℕ) : ComplexL2 →L[ℂ] Space →ᵇ ComplexVector :=
  sharpCutoffComplexRepresentativeCLM n
example (n : ℕ) (u : SpatialL2) :
    sharpCutoffComplexRepresentativeCLM n (𝓕 (complexifyL2 u)) =
      inverseL1Representative (𝓕 (complexifyL2 (sharpCutoff n u)))
        (integrable_sharpCutoff_fourier n u) := complexRepresentative_eq_inverseL1 n u
example (n : ℕ) : SpatialL2 →L[ℝ] Space →ᵇ Space := sharpCutoffRepresentativeCLM n
example (n : ℕ) (u : SpatialL2) (x : Space) :
    sharpCutoffRepresentativeCLM n u x =
      realPartVectorCLM
        (sharpCutoffComplexRepresentativeCLM n (𝓕 (complexifyL2 u)) x) :=
  sharpCutoffRepresentativeCLM_apply n u x
example (n : ℕ) (u : SpatialL2) :
    (fun x : Space => sharpCutoffRepresentativeCLM n u x) =ᵐ[volume]
      (fun x : Space => sharpCutoff n u x) := sharpCutoffRepresentative_ae n u
example (n : ℕ) (u : SpatialL2) :
    ContDiff ℝ ∞ (fun x : Space => sharpCutoffRepresentativeCLM n u x) :=
  contDiff_sharpCutoffRepresentative n u

-- Finite nonsharp fixed-n control from the explicitly constructed maps.
example (n : ℕ) :
    bernsteinConstant n =
      ‖realPartVectorCLM‖ * ‖Real.Lp.fourierTransformInvCLM Space ComplexVector‖ *
        ‖(ContinuousLinearMap.lsmul ℂ ℂ :
          ℂ →L[ℂ] ComplexVector →L[ℂ] ComplexVector)‖ * ‖cutoffMaskL2 n‖ := rfl
example (n : ℕ) : 0 ≤ bernsteinConstant n := bernsteinConstant_nonneg n
example (n : ℕ) (u : SpatialL2) :
    ‖sharpCutoffRepresentativeCLM n u‖ ≤ bernsteinConstant n * ‖u‖ :=
  norm_sharpCutoffRepresentative_le n u
example (n : ℕ) (u : SpatialL2) (x : Space) :
    ‖sharpCutoffRepresentativeCLM n u x‖ ≤ bernsteinConstant n * ‖u‖ :=
  sharpCutoffRepresentative_pointwise_le n u x

end R3EhrenfestSmoothRepresentative.ExpectedTypes

-- Exact named reports are executed only by authorized cached external CI.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.ComplexL1"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.ComplexL1
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.ComplexL1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.ComplexL1"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.ComplexL1
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.ComplexL1"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffMaskL2"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffMaskL2
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffMaskL2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffMaskL2"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffMaskL2
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffMaskL2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffMaskL2_ae"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffMaskL2_ae
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffMaskL2_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffMaskL2_ae"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffMaskL2_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffMaskL2_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_cutoffMaskL2"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_cutoffMaskL2
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_cutoffMaskL2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_cutoffMaskL2"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_cutoffMaskL2
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_cutoffMaskL2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffFrequencyL1CLM"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffFrequencyL1CLM
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffFrequencyL1CLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffFrequencyL1CLM"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffFrequencyL1CLM
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffFrequencyL1CLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffFrequencyL1_ae"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffFrequencyL1_ae
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffFrequencyL1_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffFrequencyL1_ae"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffFrequencyL1_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.cutoffFrequencyL1_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_cutoffFrequencyL1_le"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_cutoffFrequencyL1_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_cutoffFrequencyL1_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_cutoffFrequencyL1_le"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_cutoffFrequencyL1_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_cutoffFrequencyL1_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.integrable_sharpCutoff_fourier"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.integrable_sharpCutoff_fourier
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.integrable_sharpCutoff_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.integrable_sharpCutoff_fourier"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.integrable_sharpCutoff_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.integrable_sharpCutoff_fourier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.integrable_sharpCutoff_fourier_moment"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.integrable_sharpCutoff_fourier_moment
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.integrable_sharpCutoff_fourier_moment"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.integrable_sharpCutoff_fourier_moment"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.integrable_sharpCutoff_fourier_moment
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.integrable_sharpCutoff_fourier_moment"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffComplexRepresentativeCLM"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffComplexRepresentativeCLM
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffComplexRepresentativeCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffComplexRepresentativeCLM"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffComplexRepresentativeCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffComplexRepresentativeCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.complexRepresentative_eq_inverseL1"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.complexRepresentative_eq_inverseL1
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.complexRepresentative_eq_inverseL1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.complexRepresentative_eq_inverseL1"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.complexRepresentative_eq_inverseL1
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.complexRepresentative_eq_inverseL1"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentativeCLM"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentativeCLM
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentativeCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentativeCLM"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentativeCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentativeCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentativeCLM_apply"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentativeCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentativeCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentativeCLM_apply"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentativeCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentativeCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentative_ae"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentative_ae
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentative_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentative_ae"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentative_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentative_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.contDiff_sharpCutoffRepresentative"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.contDiff_sharpCutoffRepresentative
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.contDiff_sharpCutoffRepresentative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.contDiff_sharpCutoffRepresentative"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.contDiff_sharpCutoffRepresentative
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.contDiff_sharpCutoffRepresentative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.bernsteinConstant"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.bernsteinConstant
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.bernsteinConstant"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.bernsteinConstant"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.bernsteinConstant
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.bernsteinConstant"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.bernsteinConstant_nonneg"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.bernsteinConstant_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.bernsteinConstant_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.bernsteinConstant_nonneg"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.bernsteinConstant_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.bernsteinConstant_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_sharpCutoffRepresentative_le"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_sharpCutoffRepresentative_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_sharpCutoffRepresentative_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_sharpCutoffRepresentative_le"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_sharpCutoffRepresentative_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.norm_sharpCutoffRepresentative_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentative_pointwise_le"
#check @MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentative_pointwise_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentative_pointwise_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentative_pointwise_le"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentative_pointwise_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothRepresentative.sharpCutoffRepresentative_pointwise_le"

