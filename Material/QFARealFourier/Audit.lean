import QFARealFourier.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform ComplexConjugate
open scoped BigOperators SchwartzMap FourierTransform

namespace QFARealFourier.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.RealFourier
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation

-- The physical domain and both L2 fibers are literal full-volume Euclidean spaces.
example : MethbokeAddon.QuasiFeffermanA.Space = EuclideanSpace ℝ (Fin 3) := rfl
example : ComplexVector = EuclideanSpace ℂ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl

-- Actual componentwise vector operations, their exact types and literal formulas.
example : ComplexVector →ₗᵢ[ℝ] ComplexVector := conjugateVectorLI
example (z : ComplexVector) :
    conjugateVectorLI z = WithLp.toLp 2 (fun j : Fin 3 => conj (z j)) := rfl
example (z : ComplexVector) (j : Fin 3) :
    conjugateVectorLI z j = conj (z j) := conjugateVectorLI_apply z j
example (c : ℂ) (z : ComplexVector) :
    conjugateVectorLI (c • z) = conj c • conjugateVectorLI z :=
  conjugateVectorLI_smul c z
example : ComplexVector →L[ℝ] MethbokeAddon.QuasiFeffermanA.Space := realPartVectorCLM
example (z : ComplexVector) :
    realPartVectorCLM z = WithLp.toLp 2 (fun j : Fin 3 => (z j).re) := rfl
example (z : ComplexVector) (j : Fin 3) :
    realPartVectorCLM z j = (z j).re := realPartVectorCLM_apply z j
example (z : ComplexVector) (h : conjugateVectorLI z = z) :
    complexifyVectorLI (realPartVectorCLM z) = z :=
  complexify_realPartVector_of_conjugate_eq z h

-- Actual L2 postcomposition, including representative identities and explicit real preimages.
example : ComplexL2 →L[ℝ] ComplexL2 := conjugateL2CLM
example : conjugateL2CLM = conjugateVectorLI.toContinuousLinearMap.compLpL 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example (f : ComplexL2) :
    (fun x : MethbokeAddon.QuasiFeffermanA.Space => conjugateL2CLM f x) =ᵐ[volume]
      (fun x : MethbokeAddon.QuasiFeffermanA.Space => conjugateVectorLI (f x)) :=
  conjugateL2_ae f
example (u : SpatialL2) : conjugateL2CLM (complexifyL2 u) = complexifyL2 u :=
  conjugateL2_complexify u
example : ComplexL2 →L[ℝ] SpatialL2 := realPartL2CLM
example : realPartL2CLM = realPartVectorCLM.compLpL 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example (f : ComplexL2) :
    (fun x : MethbokeAddon.QuasiFeffermanA.Space => realPartL2CLM f x) =ᵐ[volume]
      (fun x : MethbokeAddon.QuasiFeffermanA.Space => realPartVectorCLM (f x)) :=
  realPartL2_ae f
example (u : SpatialL2) : realPartL2CLM (complexifyL2 u) = u :=
  realPartL2_complexify u
example (f : ComplexL2) (h : conjugateL2CLM f = f) :
    complexifyL2 (realPartL2CLM f) = f := complexify_realPartL2_of_conjugate_eq f h
example (f : ComplexL2) :
    (∃ u : SpatialL2, complexifyL2 u = f) ↔ conjugateL2CLM f = f :=
  exists_complexify_iff_conjugate_eq f

-- Reflection is the actual volume-preserving Euclidean map, not a supplied abstract operator.
example (p : MethbokeAddon.QuasiFeffermanA.Space → Prop)
    (h : ∀ᵐ x : MethbokeAddon.QuasiFeffermanA.Space ∂volume, p x) :
    ∀ᵐ x : MethbokeAddon.QuasiFeffermanA.Space ∂volume, p (-x) := ae_neg_of_ae h
example : ComplexL2 →ₗᵢ[ℂ] ComplexL2 := reflectL2LI
example : reflectL2LI =
    Lp.compMeasurePreservingₗᵢ ℂ
      (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin 3)))
      (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin 3))).measurePreserving := rfl
example (f : ComplexL2) :
    (fun x : MethbokeAddon.QuasiFeffermanA.Space => reflectL2LI f x) =ᵐ[volume]
      (fun x : MethbokeAddon.QuasiFeffermanA.Space => f (-x)) := reflectL2_ae f
example : ComplexL2 →L[ℝ] ComplexL2 := hermitianL2CLM
example : hermitianL2CLM =
    conjugateL2CLM.comp (reflectL2LI.toContinuousLinearMap.restrictScalars ℝ) := rfl
example (f : ComplexL2) :
    (fun x : MethbokeAddon.QuasiFeffermanA.Space => hermitianL2CLM f x) =ᵐ[volume]
      (fun x : MethbokeAddon.QuasiFeffermanA.Space => conjugateVectorLI (f (-x))) :=
  hermitianL2_ae f

-- Complete Fourier transport and both directions of both actual range characterizations.
example (f : ComplexL2) :
    𝓕 (conjugateL2CLM f) = hermitianL2CLM (𝓕 f) := fourier_conjugateL2 f
example (u : SpatialL2) :
    hermitianL2CLM (𝓕 (complexifyL2 u)) = 𝓕 (complexifyL2 u) :=
  hermitian_fourier_complexify u
example (f : ComplexL2) :
    conjugateL2CLM f = f ↔ hermitianL2CLM (𝓕 f) = 𝓕 f :=
  conjugate_eq_iff_hermitian_fourier_eq f
example (f : ComplexL2) :
    (∃ u : SpatialL2, complexifyL2 u = f) ↔ hermitianL2CLM (𝓕 f) = 𝓕 f :=
  exists_complexify_iff_hermitian_fourier_eq f
example (f : ComplexL2) :
    (∃ u : SpatialL2, 𝓕 (complexifyL2 u) = f) ↔ hermitianL2CLM f = f :=
  exists_fourier_complexify_iff_hermitian_eq f

end QFARealFourier.ExpectedTypes

-- Ordered, named full type and axiom reports; external verification only.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI_apply"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI_smul"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI_smul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI_smul"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateVectorLI_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartVectorCLM"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.realPartVectorCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartVectorCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartVectorCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.realPartVectorCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartVectorCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartVectorCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.realPartVectorCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartVectorCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartVectorCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.realPartVectorCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartVectorCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.complexify_realPartVector_of_conjugate_eq"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.complexify_realPartVector_of_conjugate_eq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.complexify_realPartVector_of_conjugate_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.complexify_realPartVector_of_conjugate_eq"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.complexify_realPartVector_of_conjugate_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.complexify_realPartVector_of_conjugate_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2CLM"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2CLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2CLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2CLM"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2CLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2CLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2_ae"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2_complexify"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2_complexify
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2_complexify"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2_complexify"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2_complexify
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugateL2_complexify"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2CLM"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2CLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2CLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2CLM"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2CLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2CLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2_ae"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2_complexify"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2_complexify
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2_complexify"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2_complexify"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2_complexify
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.realPartL2_complexify"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.complexify_realPartL2_of_conjugate_eq"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.complexify_realPartL2_of_conjugate_eq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.complexify_realPartL2_of_conjugate_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.complexify_realPartL2_of_conjugate_eq"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.complexify_realPartL2_of_conjugate_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.complexify_realPartL2_of_conjugate_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.exists_complexify_iff_conjugate_eq"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.exists_complexify_iff_conjugate_eq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.exists_complexify_iff_conjugate_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.exists_complexify_iff_conjugate_eq"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.exists_complexify_iff_conjugate_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.exists_complexify_iff_conjugate_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.ae_neg_of_ae"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.ae_neg_of_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.ae_neg_of_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.ae_neg_of_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.ae_neg_of_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.ae_neg_of_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.reflectL2LI"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.reflectL2LI
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.reflectL2LI"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.reflectL2LI"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.reflectL2LI
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.reflectL2LI"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.reflectL2_ae"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.reflectL2_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.reflectL2_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.reflectL2_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.reflectL2_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.reflectL2_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.hermitianL2CLM"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.hermitianL2CLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.hermitianL2CLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.hermitianL2CLM"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.hermitianL2CLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.hermitianL2CLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.hermitianL2_ae"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.hermitianL2_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.hermitianL2_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.hermitianL2_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.hermitianL2_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.hermitianL2_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.fourier_conjugateL2"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.fourier_conjugateL2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.fourier_conjugateL2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.fourier_conjugateL2"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.fourier_conjugateL2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.fourier_conjugateL2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.hermitian_fourier_complexify"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.hermitian_fourier_complexify
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.hermitian_fourier_complexify"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.hermitian_fourier_complexify"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.hermitian_fourier_complexify
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.hermitian_fourier_complexify"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugate_eq_iff_hermitian_fourier_eq"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.conjugate_eq_iff_hermitian_fourier_eq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugate_eq_iff_hermitian_fourier_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugate_eq_iff_hermitian_fourier_eq"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.conjugate_eq_iff_hermitian_fourier_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.conjugate_eq_iff_hermitian_fourier_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.exists_complexify_iff_hermitian_fourier_eq"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.exists_complexify_iff_hermitian_fourier_eq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.exists_complexify_iff_hermitian_fourier_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.exists_complexify_iff_hermitian_fourier_eq"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.exists_complexify_iff_hermitian_fourier_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.exists_complexify_iff_hermitian_fourier_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.exists_fourier_complexify_iff_hermitian_eq"
#check @MethbokeAddon.QuasiFeffermanA.RealFourier.exists_fourier_complexify_iff_hermitian_eq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealFourier.exists_fourier_complexify_iff_hermitian_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealFourier.exists_fourier_complexify_iff_hermitian_eq"
#print axioms MethbokeAddon.QuasiFeffermanA.RealFourier.exists_fourier_complexify_iff_hermitian_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealFourier.exists_fourier_complexify_iff_hermitian_eq"
