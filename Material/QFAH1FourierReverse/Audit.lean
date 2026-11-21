import QFAH1FourierReverse.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap LineDeriv FourierTransform

namespace QFAH1FourierReverse.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.H1Fourier
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation

-- Literal carriers and physical compact-test semantics are pinned independently.
example : MethbokeAddon.QuasiFeffermanA.Space = EuclideanSpace ℝ (Fin 3) := rfl
example : RealL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl

example (u du : RealL2) (e : MethbokeAddon.QuasiFeffermanA.Space) :
    RealTestWeakDirectionalDerivative u du e ↔
      ∀ (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ x : MethbokeAddon.QuasiFeffermanA.Space, fderiv ℝ ψ x e • u x) =
          -(∫ x : MethbokeAddon.QuasiFeffermanA.Space, ψ x • du x) := Iff.rfl

example (u du : ComplexL2) (e : MethbokeAddon.QuasiFeffermanA.Space) :
    RealTestWeakDirectionalDerivative u du e ↔
      ∀ (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ x : MethbokeAddon.QuasiFeffermanA.Space, fderiv ℝ ψ x e • u x) =
          -(∫ x : MethbokeAddon.QuasiFeffermanA.Space, ψ x • du x) := Iff.rfl

example (u : SpatialL2) (G : Fin 3 → SpatialL2) :
    SpatialWeakGradient u G ↔
      ∀ (j : Fin 3) (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ),
        ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ x : MethbokeAddon.QuasiFeffermanA.Space, fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) • u x) =
          -(∫ x : MethbokeAddon.QuasiFeffermanA.Space, ψ x • G j x) := Iff.rfl

-- R01: the supplied L2 representative identity is the only multiplier premise.
example (q h : ComplexL2) (c : ℂ) (m : MethbokeAddon.QuasiFeffermanA.Space → ℝ)
    (hm : m.HasTemperateGrowth)
    (hae : (fun x : MethbokeAddon.QuasiFeffermanA.Space => q x) =ᵐ[volume]
      (fun x : MethbokeAddon.QuasiFeffermanA.Space => (c * (m x : ℂ)) • h x)) :
    (q : 𝓢'(MethbokeAddon.QuasiFeffermanA.Space, ComplexVector)) =
      c • TemperedDistribution.smulLeftCLM ComplexVector
        (fun x : MethbokeAddon.QuasiFeffermanA.Space => (m x : ℂ)) (h : 𝓢'(MethbokeAddon.QuasiFeffermanA.Space, ComplexVector)) :=
  const_smul_real_multiplier_distribution_of_ae q h c m hm hae

-- R02: no supplied derivative-distribution identity or PDE is assumed.
example (u du : ComplexL2) (e : MethbokeAddon.QuasiFeffermanA.Space)
    (hae : (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => (𝓕 du : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => ((2 * Real.pi * Complex.I) *
        (inner ℝ ξ e : ℂ)) • (𝓕 u : ComplexL2) ξ)) :
    (du : 𝓢'(MethbokeAddon.QuasiFeffermanA.Space, ComplexVector)) =
      ∂_{e} (u : 𝓢'(MethbokeAddon.QuasiFeffermanA.Space, ComplexVector)) :=
  temperedDerivative_of_fourier_ae hae

-- R03: all compact smooth real tests, retaining the actual negative sign.
example (u du : ComplexL2) (e : MethbokeAddon.QuasiFeffermanA.Space)
    (hweak : (du : 𝓢'(MethbokeAddon.QuasiFeffermanA.Space, ComplexVector)) =
      ∂_{e} (u : 𝓢'(MethbokeAddon.QuasiFeffermanA.Space, ComplexVector))) :
    ∀ (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : MethbokeAddon.QuasiFeffermanA.Space, fderiv ℝ ψ x e • u x) =
        -(∫ x : MethbokeAddon.QuasiFeffermanA.Space, ψ x • du x) :=
  realTestWeakDirectionalDerivative_of_temperedDerivative hweak

-- R04: reflection through the actual native complexification.
example (u du : RealL2) (e : MethbokeAddon.QuasiFeffermanA.Space)
    (hweak : ∀ (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : MethbokeAddon.QuasiFeffermanA.Space, fderiv ℝ ψ x e • complexifyL2 u x) =
        -(∫ x : MethbokeAddon.QuasiFeffermanA.Space, ψ x • complexifyL2 du x)) :
    ∀ (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : MethbokeAddon.QuasiFeffermanA.Space, fderiv ℝ ψ x e • u x) =
        -(∫ x : MethbokeAddon.QuasiFeffermanA.Space, ψ x • du x) :=
  realTestWeakDirectionalDerivative_of_complexify hweak

-- R05: the complete complex reverse implication.
example (u du : ComplexL2) (e : MethbokeAddon.QuasiFeffermanA.Space)
    (hae : (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => (𝓕 du : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => ((2 * Real.pi * Complex.I) *
        (inner ℝ ξ e : ℂ)) • (𝓕 u : ComplexL2) ξ)) :
    ∀ (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : MethbokeAddon.QuasiFeffermanA.Space, fderiv ℝ ψ x e • u x) =
        -(∫ x : MethbokeAddon.QuasiFeffermanA.Space, ψ x • du x) :=
  realTestWeakDirectionalDerivative_of_fourier_ae hae

-- R06: supplied real fields, no extra spectral integrability assumption.
example (u du : RealL2) (e : MethbokeAddon.QuasiFeffermanA.Space)
    (hae : (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => (𝓕 (complexifyL2 du) : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => ((2 * Real.pi * Complex.I) *
        (inner ℝ ξ e : ℂ)) • (𝓕 (complexifyL2 u) : ComplexL2) ξ)) :
    ∀ (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : MethbokeAddon.QuasiFeffermanA.Space, fderiv ℝ ψ x e • u x) =
        -(∫ x : MethbokeAddon.QuasiFeffermanA.Space, ψ x • du x) :=
  realTestWeakDirectionalDerivative_of_complexify_fourier_ae hae

-- R07: both directions of the exact supplied directional-gradient equivalence.
example (u du : RealL2) (e : MethbokeAddon.QuasiFeffermanA.Space) :
    (∀ (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : MethbokeAddon.QuasiFeffermanA.Space, fderiv ℝ ψ x e • u x) =
        -(∫ x : MethbokeAddon.QuasiFeffermanA.Space, ψ x • du x)) ↔
      (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => (𝓕 (complexifyL2 du) : ComplexL2) ξ) =ᵐ[volume]
        (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => ((2 * Real.pi * Complex.I) *
          (inner ℝ ξ e : ℂ)) • (𝓕 (complexifyL2 u) : ComplexL2) ξ) :=
  realTestWeakDirectionalDerivative_iff_complexify_fourier_ae u du e

-- R08: all three literal coordinate derivatives on the same real fields.
example (u : SpatialL2) (G : Fin 3 → SpatialL2) :
    (∀ (j : Fin 3) (ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : MethbokeAddon.QuasiFeffermanA.Space, fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) • u x) =
        -(∫ x : MethbokeAddon.QuasiFeffermanA.Space, ψ x • G j x)) ↔
      ∀ᵐ ξ : MethbokeAddon.QuasiFeffermanA.Space ∂volume, ∀ j : Fin 3,
        (𝓕 (complexifyL2 (G j)) : ComplexL2) ξ =
          ((2 * Real.pi * Complex.I) * (inner ℝ ξ (EuclideanSpace.single j (1 : ℝ)) : ℂ)) •
            (𝓕 (complexifyL2 u) : ComplexL2) ξ :=
  spatialWeakGradient_iff_fourier_ae u G

end QFAH1FourierReverse.ExpectedTypes

-- NAMED REPORTS: executed only by authorized external CI.
#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.const_smul_real_multiplier_distribution_of_ae"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.const_smul_real_multiplier_distribution_of_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.const_smul_real_multiplier_distribution_of_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.const_smul_real_multiplier_distribution_of_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.const_smul_real_multiplier_distribution_of_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.const_smul_real_multiplier_distribution_of_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.temperedDerivative_of_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.temperedDerivative_of_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.temperedDerivative_of_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.temperedDerivative_of_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.temperedDerivative_of_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.temperedDerivative_of_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_temperedDerivative"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_temperedDerivative
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_temperedDerivative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_temperedDerivative"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_temperedDerivative
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_temperedDerivative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_complexify"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_complexify
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_complexify"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_complexify"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_complexify
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_complexify"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_complexify_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_complexify_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_complexify_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_complexify_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_complexify_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_of_complexify_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_iff_complexify_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_iff_complexify_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_iff_complexify_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_iff_complexify_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_iff_complexify_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.realTestWeakDirectionalDerivative_iff_complexify_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.spatialWeakGradient_iff_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.H1Fourier.spatialWeakGradient_iff_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.spatialWeakGradient_iff_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.H1Fourier.spatialWeakGradient_iff_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.H1Fourier.spatialWeakGradient_iff_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.H1Fourier.spatialWeakGradient_iff_fourier_ae"

