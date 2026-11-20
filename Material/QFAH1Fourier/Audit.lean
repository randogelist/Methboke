import QFAH1Fourier.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

-- Passive independently stated consumer assertions for external audit only.
-- Root supplies the package import, full-printer options and named sentinels.
-- No local Lean execution.

noncomputable section
open MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap LineDeriv FourierTransform

namespace QFAH1Fourier.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.H1Fourier
open QFA.Endpoints.Agmon
open QFA.Endpoints.Representation

-- Literal physical carriers and compact-test semantics.
example : Space = EuclideanSpace ℝ (Fin 3) := rfl
example : RealL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl

example (u du : RealL2) (e : Space) :
    RealTestWeakDirectionalDerivative u du e ↔
      ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ x : Space, (fderiv ℝ ψ x e) • u x) =
          -(∫ x : Space, ψ x • du x) := Iff.rfl

example (u du : ComplexL2) (e : Space) :
    RealTestWeakDirectionalDerivative u du e ↔
      ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ x : Space, (fderiv ℝ ψ x e) • u x) =
          -(∫ x : Space, ψ x • du x) := Iff.rfl

example (u : SpatialL2) (G : Fin 3 → SpatialL2) :
    SpatialWeakGradient u G ↔
      ∀ (j : Fin 3) (ψ : Space → ℝ),
        ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ x : Space, (fderiv ℝ ψ x (EuclideanSpace.single j 1)) • u x) =
          -(∫ x : Space, ψ x • G j x) := Iff.rfl

-- F01: only a Schwartz scalar function and one direction.
example (ψ : 𝓢(Space, ℝ)) (e : Space) :
    ∂_{e} (ψ.postcompCLM Complex.ofRealCLM) =
      (∂_{e} ψ).postcompCLM Complex.ofRealCLM :=
  lineDeriv_postcomp_ofReal ψ e

-- F02/F03: complete literal compact-real-test premise, no density port.
example (u du : ComplexL2) (e : Space)
    (h : ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x e • u x) =
        -(∫ x : Space, ψ x • du x)) :
    (du : 𝓢'(Space, ComplexVector)) =
      ∂_{e} (u : 𝓢'(Space, ComplexVector)) :=
  temperedDerivative_of_realTestWeakDirectionalDerivative h

-- F06: actual real L2 weak derivative transported by actual complexification.
example (u du : RealL2) (e : Space)
    (h : ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x e • u x) =
        -(∫ x : Space, ψ x • du x)) :
    (complexifyL2 du : 𝓢'(Space, ComplexVector)) =
      ∂_{e} (complexifyL2 u : 𝓢'(Space, ComplexVector)) :=
  complexify_temperedDerivative_of_realTestWeakDirectionalDerivative h

-- F04: the actual supplied directional derivative distribution identity.
example (u du : ComplexL2) (e : Space)
    (h : (du : 𝓢'(Space, ComplexVector)) =
      ∂_{e} (u : 𝓢'(Space, ComplexVector))) :
    ((𝓕 du : ComplexL2) : 𝓢'(Space, ComplexVector)) =
      (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM ComplexVector
          (fun ξ : Space => (inner ℝ ξ e : ℂ))
          ((𝓕 u : ComplexL2) : 𝓢'(Space, ComplexVector)) :=
  fourier_directionalDerivative_distribution h

-- F05: no derivative-density, frequency-integrability or H2 premise.
example (u du : ComplexL2) (e : Space)
    (h : (du : 𝓢'(Space, ComplexVector)) =
      ∂_{e} (u : 𝓢'(Space, ComplexVector))) :
    (fun ξ : Space => (𝓕 du : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space => ((2 * Real.pi * Complex.I) *
        (inner ℝ ξ e : ℂ)) • (𝓕 u : ComplexL2) ξ) :=
  fourier_directionalDerivative_ae h

-- Compact-real-test version of the complex L2 identity.
example (u du : ComplexL2) (e : Space)
    (h : ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x e • u x) =
        -(∫ x : Space, ψ x • du x)) :
    (fun ξ : Space => (𝓕 du : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space => ((2 * Real.pi * Complex.I) *
        (inner ℝ ξ e : ℂ)) • (𝓕 u : ComplexL2) ξ) :=
  fourier_of_realTestWeakDirectionalDerivative h

-- Compact-real-test version for native real L2 fields.
example (u du : RealL2) (e : Space)
    (h : ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x e • u x) =
        -(∫ x : Space, ψ x • du x)) :
    (fun ξ : Space => (𝓕 (complexifyL2 du) : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space => ((2 * Real.pi * Complex.I) *
        (inner ℝ ξ e : ℂ)) • (𝓕 (complexifyL2 u) : ComplexL2) ξ) :=
  complexify_fourier_of_realTestWeakDirectionalDerivative h

-- F07: all three actual native coordinate derivatives; no Laplacian witness.
example (u : SpatialL2) (G : Fin 3 → SpatialL2)
    (h : ∀ (j : Fin 3) (ψ : Space → ℝ),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single j 1) • u x) =
        -(∫ x : Space, ψ x • G j x)) :
    ∀ᵐ ξ : Space ∂volume, ∀ j : Fin 3,
      (𝓕 (complexifyL2 (G j)) : ComplexL2) ξ =
        ((2 * Real.pi * Complex.I) * (inner ℝ ξ (EuclideanSpace.single j 1) : ℂ)) •
          (𝓕 (complexifyL2 u) : ComplexL2) ξ :=
  spatialWeakGradient_fourier_ae h

end QFAH1Fourier.ExpectedTypes

-- NAMED REPORTS: generated text, executed only by authorized external CI.
#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.lineDeriv_postcomp_ofReal"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.lineDeriv_postcomp_ofReal
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.lineDeriv_postcomp_ofReal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.lineDeriv_postcomp_ofReal"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.lineDeriv_postcomp_ofReal
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.lineDeriv_postcomp_ofReal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.temperedDerivative_of_realTestWeakDirectionalDerivative"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.temperedDerivative_of_realTestWeakDirectionalDerivative
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.temperedDerivative_of_realTestWeakDirectionalDerivative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.temperedDerivative_of_realTestWeakDirectionalDerivative"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.temperedDerivative_of_realTestWeakDirectionalDerivative
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.temperedDerivative_of_realTestWeakDirectionalDerivative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.complexify_temperedDerivative_of_realTestWeakDirectionalDerivative"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.complexify_temperedDerivative_of_realTestWeakDirectionalDerivative
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.complexify_temperedDerivative_of_realTestWeakDirectionalDerivative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.complexify_temperedDerivative_of_realTestWeakDirectionalDerivative"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.complexify_temperedDerivative_of_realTestWeakDirectionalDerivative
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.complexify_temperedDerivative_of_realTestWeakDirectionalDerivative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_directionalDerivative_distribution"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_directionalDerivative_distribution
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_directionalDerivative_distribution"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_directionalDerivative_distribution"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_directionalDerivative_distribution
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_directionalDerivative_distribution"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_directionalDerivative_ae"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_directionalDerivative_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_directionalDerivative_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_directionalDerivative_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_directionalDerivative_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_directionalDerivative_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_of_realTestWeakDirectionalDerivative"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_of_realTestWeakDirectionalDerivative
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_of_realTestWeakDirectionalDerivative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_of_realTestWeakDirectionalDerivative"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_of_realTestWeakDirectionalDerivative
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.fourier_of_realTestWeakDirectionalDerivative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.complexify_fourier_of_realTestWeakDirectionalDerivative"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.complexify_fourier_of_realTestWeakDirectionalDerivative
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.complexify_fourier_of_realTestWeakDirectionalDerivative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.complexify_fourier_of_realTestWeakDirectionalDerivative"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.complexify_fourier_of_realTestWeakDirectionalDerivative
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.complexify_fourier_of_realTestWeakDirectionalDerivative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.spatialWeakGradient_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.spatialWeakGradient_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.spatialWeakGradient_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.spatialWeakGradient_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.spatialWeakGradient_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.spatialWeakGradient_fourier_ae"
