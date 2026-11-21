import QFARealEvenMultipliers.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform ContDiff NNReal

namespace QFARealEvenMultipliers.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers
open MethbokeAddon.QuasiFeffermanA.RealFourier
open QFA.Endpoints.Representation
open QFA.Endpoints.Agmon (ComplexVector ComplexL2)

example : Space = EuclideanSpace ℝ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl

-- The symbol record asks only for elementary properties of a scalar function.
example (m : Space → ℝ) (hm : Measurable m)
    (heven : ∀ ξ : Space, m (-ξ) = m ξ) (C : ℝ≥0)
    (hbound : ∀ ξ : Space, ‖m ξ‖ ≤ (C : ℝ)) : RealEvenSymbol :=
  ⟨m, hm, heven, C, hbound⟩
example (m : RealEvenSymbol) : Measurable m.value := m.measurable
example (m : RealEvenSymbol) (ξ : Space) : m.value (-ξ) = m.value ξ := m.even ξ
example (m : RealEvenSymbol) (ξ : Space) : ‖m.value ξ‖ ≤ (m.bound : ℝ) := m.norm_le ξ

example (m : RealEvenSymbol) (f : ComplexL2) :
    MemLp (fun ξ : Space => (m.value ξ : ℂ) • f ξ) 2 volume := memLp_symbol_smul m f
example (m : RealEvenSymbol) (f : ComplexL2) :
    frequencyMultiplier m f =
      (memLp_symbol_smul m f).toLp (fun ξ : Space => (m.value ξ : ℂ) • f ξ) := rfl
example (m : RealEvenSymbol) (f : ComplexL2) :
    (fun ξ : Space => frequencyMultiplier m f ξ) =ᵐ[volume]
      (fun ξ : Space => (m.value ξ : ℂ) • f ξ) := frequencyMultiplier_ae m f
example (m : RealEvenSymbol) (f : ComplexL2) :
    ‖frequencyMultiplier m f‖ ≤ (m.bound : ℝ) * ‖f‖ := norm_frequencyMultiplier_le m f
example (m : RealEvenSymbol) (f g : ComplexL2) :
    frequencyMultiplier m (f + g) = frequencyMultiplier m f + frequencyMultiplier m g :=
  frequencyMultiplier_add m f g
example (m : RealEvenSymbol) (c : ℂ) (f : ComplexL2) :
    frequencyMultiplier m (c • f) = c • frequencyMultiplier m f := frequencyMultiplier_smul m c f
example (m : RealEvenSymbol) : frequencyMultiplier m 0 = 0 := frequencyMultiplier_zero m
example (m : RealEvenSymbol) : ComplexL2 →L[ℂ] ComplexL2 := frequencyMultiplierCLM m
example (m : RealEvenSymbol) (f : ComplexL2) :
    frequencyMultiplierCLM m f = frequencyMultiplier m f := frequencyMultiplierCLM_apply m f

-- The constructed involution is the actual conjugate-reflection, and its
-- commutation is a conclusion rather than a premise in the symbol record.
example (f : ComplexL2) :
    (fun ξ : Space => hermitianL2CLM f ξ) =ᵐ[volume]
      (fun ξ : Space => conjugateVectorLI (f (-ξ))) := hermitianL2_ae f
example (m : RealEvenSymbol) (f : ComplexL2) :
    hermitianL2CLM (frequencyMultiplier m f) = frequencyMultiplier m (hermitianL2CLM f) :=
  hermitian_frequencyMultiplier m f
example (m : RealEvenSymbol) (u : SpatialL2) :
    realFourierMultiplier m u = realPartL2CLM
      (𝓕⁻ (frequencyMultiplier m (𝓕 (complexifyL2 u)))) := rfl
example (m : RealEvenSymbol) (u : SpatialL2) :
    complexifyL2 (realFourierMultiplier m u) =
      𝓕⁻ (frequencyMultiplier m (𝓕 (complexifyL2 u))) := complexify_realFourierMultiplier m u
example (m : RealEvenSymbol) (u : SpatialL2) :
    (𝓕 (complexifyL2 (realFourierMultiplier m u)) : ComplexL2) =
      frequencyMultiplier m (𝓕 (complexifyL2 u)) := fourier_complexify_realFourierMultiplier m u
example (m : RealEvenSymbol) (u : SpatialL2) :
    (fun ξ : Space => (𝓕 (complexifyL2 (realFourierMultiplier m u)) : ComplexL2) ξ)
      =ᵐ[volume] (fun ξ : Space =>
        (m.value ξ : ℂ) • (𝓕 (complexifyL2 u) : ComplexL2) ξ) :=
  fourier_complexify_realFourierMultiplier_ae m u

example (m : RealEvenSymbol) : SpatialL2 →L[ℝ] SpatialL2 := realFourierMultiplierCLM m
example (m : RealEvenSymbol) (u : SpatialL2) :
    realFourierMultiplierCLM m u = realFourierMultiplier m u := realFourierMultiplierCLM_apply m u
example (m : RealEvenSymbol) (u : SpatialL2) :
    realFourierMultiplierCLM m u = realPartL2CLM
      (𝓕⁻ (frequencyMultiplier m (𝓕 (complexifyL2 u)))) := rfl
example (m : RealEvenSymbol) (u v : SpatialL2) :
    realFourierMultiplier m (u + v) = realFourierMultiplier m u + realFourierMultiplier m v :=
  realFourierMultiplier_add m u v
example (m : RealEvenSymbol) (r : ℝ) (u : SpatialL2) :
    realFourierMultiplier m (r • u) = r • realFourierMultiplier m u := realFourierMultiplier_smul m r u
example (m : RealEvenSymbol) : realFourierMultiplier m 0 = 0 := realFourierMultiplier_zero m
example (m : RealEvenSymbol) (u : SpatialL2) :
    ‖realFourierMultiplier m u‖ ≤ (m.bound : ℝ) * ‖u‖ := norm_realFourierMultiplier_le m u

example (m : RealEvenSymbol) (u v : SpatialL2)
    (h : (fun ξ : Space => (𝓕 (complexifyL2 v) : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space => (m.value ξ : ℂ) • (𝓕 (complexifyL2 u) : ComplexL2) ξ)) :
    v = realFourierMultiplier m u := realFourierMultiplier_eq_of_fourier_ae m u v h
example (m : RealEvenSymbol) (f g : ComplexL2) (a : Space → ℂ)
    (h : (fun ξ : Space => g ξ) =ᵐ[volume] (fun ξ : Space => a ξ • f ξ)) :
    (fun ξ : Space => frequencyMultiplier m g ξ) =ᵐ[volume]
      (fun ξ : Space => a ξ • frequencyMultiplier m f ξ) := frequencyMultiplier_multiplier_ae m f g a h

-- The original physical weak test and every coordinate direction are retained.
example (v : SpatialL2) (G : Fin 3 → SpatialL2) : SpatialWeakGradient v G ↔
    ∀ (j : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) • v x) =
        -(∫ x : Space, ψ x • G j x) := Iff.rfl
example (m : RealEvenSymbol) (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (h : ∀ (j : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) • v x) =
        -(∫ x : Space, ψ x • G j x)) :
    ∀ (j : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) •
        realFourierMultiplier m v x) =
          -(∫ x : Space, ψ x • realFourierMultiplier m (G j) x) :=
  spatialWeakGradient_realFourierMultiplier m h

end QFARealEvenMultipliers.ExpectedTypes

-- Ordered exact-type and named axiom reports.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.RealEvenSymbol"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.RealEvenSymbol
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.RealEvenSymbol"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.RealEvenSymbol"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.RealEvenSymbol
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.RealEvenSymbol"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.memLp_symbol_smul"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.memLp_symbol_smul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.memLp_symbol_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.memLp_symbol_smul"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.memLp_symbol_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.memLp_symbol_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_ae"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.norm_frequencyMultiplier_le"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.norm_frequencyMultiplier_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.norm_frequencyMultiplier_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.norm_frequencyMultiplier_le"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.norm_frequencyMultiplier_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.norm_frequencyMultiplier_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_add"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_add
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_add"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_add
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_smul"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_smul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_smul"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_zero"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplierCLM"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplierCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplierCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplierCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplierCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplierCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplierCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplierCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplierCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplierCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplierCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplierCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.hermitian_frequencyMultiplier"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.hermitian_frequencyMultiplier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.hermitian_frequencyMultiplier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.hermitian_frequencyMultiplier"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.hermitian_frequencyMultiplier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.hermitian_frequencyMultiplier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.complexify_realFourierMultiplier"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.complexify_realFourierMultiplier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.complexify_realFourierMultiplier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.complexify_realFourierMultiplier"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.complexify_realFourierMultiplier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.complexify_realFourierMultiplier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.fourier_complexify_realFourierMultiplier"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.fourier_complexify_realFourierMultiplier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.fourier_complexify_realFourierMultiplier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.fourier_complexify_realFourierMultiplier"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.fourier_complexify_realFourierMultiplier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.fourier_complexify_realFourierMultiplier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.fourier_complexify_realFourierMultiplier_ae"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.fourier_complexify_realFourierMultiplier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.fourier_complexify_realFourierMultiplier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.fourier_complexify_realFourierMultiplier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.fourier_complexify_realFourierMultiplier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.fourier_complexify_realFourierMultiplier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplierCLM"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplierCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplierCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplierCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplierCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplierCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplierCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplierCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplierCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplierCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplierCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplierCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_add"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_add
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_add"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_add
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_smul"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_smul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_smul"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_zero"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.norm_realFourierMultiplier_le"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.norm_realFourierMultiplier_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.norm_realFourierMultiplier_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.norm_realFourierMultiplier_le"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.norm_realFourierMultiplier_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.norm_realFourierMultiplier_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_eq_of_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_eq_of_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_eq_of_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_eq_of_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_eq_of_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.realFourierMultiplier_eq_of_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_multiplier_ae"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_multiplier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_multiplier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_multiplier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_multiplier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.frequencyMultiplier_multiplier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.spatialWeakGradient_realFourierMultiplier"
#check @MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.spatialWeakGradient_realFourierMultiplier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.spatialWeakGradient_realFourierMultiplier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.spatialWeakGradient_realFourierMultiplier"
#print axioms MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.spatialWeakGradient_realFourierMultiplier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers.spatialWeakGradient_realFourierMultiplier"
