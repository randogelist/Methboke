import QFARealSectorL2.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform

namespace QFARealSectorL2.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.RealFourier
open MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers
open MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation

-- Actual full-volume real/complex L2 fibers and the registered frequency restriction.
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example (i : Fin 6) (f : ComplexL2) :
    fourierSector i f = 𝓕⁻ (frequencySector i (𝓕 f)) := rfl

-- Reality is proved for the constructed sector, with no reality-preservation premise.
example (i : Fin 6) (f : ComplexL2) :
    hermitianL2CLM (frequencySector i f) = frequencySector i (hermitianL2CLM f) :=
  hermitian_frequencySector i f
example (i : Fin 6) (u : SpatialL2) :
    conjugateL2CLM (fourierSector i (complexifyL2 u)) =
      fourierSector i (complexifyL2 u) := conjugate_fourierSector_complexify i u

-- The real operator is the actual real part of the inverse-Fourier sharp restriction.
example : Fin 6 → SpatialL2 → SpatialL2 := realFourierSector
example (i : Fin 6) (u : SpatialL2) :
    realFourierSector i u = realPartL2CLM
      (𝓕⁻ (frequencySector i (𝓕 (complexifyL2 u)))) := rfl
example (i : Fin 6) (u : SpatialL2) :
    complexifyL2 (realFourierSector i u) = fourierSector i (complexifyL2 u) :=
  complexify_realFourierSector i u
example (i : Fin 6) : SpatialL2 →L[ℝ] SpatialL2 := realFourierSectorCLM i
example (i : Fin 6) : realFourierSectorCLM i =
    realPartL2CLM.comp (((fourierSectorCLM i).restrictScalars ℝ).comp
      complexifyL2LI.toContinuousLinearMap) := rfl
example (i : Fin 6) (u : SpatialL2) :
    realFourierSectorCLM i u = realFourierSector i u := realFourierSectorCLM_apply i u

-- All real algebraic and norm assertions retain their complete quantifiers.
example (i : Fin 6) (u v : SpatialL2) :
    realFourierSector i (u + v) = realFourierSector i u + realFourierSector i v :=
  realFourierSector_add i u v
example (i : Fin 6) (r : ℝ) (u : SpatialL2) :
    realFourierSector i (r • u) = r • realFourierSector i u :=
  realFourierSector_smul i r u
example (i : Fin 6) : realFourierSector i 0 = 0 := realFourierSector_zero i
example (i : Fin 6) (u : SpatialL2) : ‖realFourierSector i u‖ ≤ ‖u‖ :=
  norm_realFourierSector_le i u
example (i : Fin 6) (u : SpatialL2) :
    realFourierSector i (realFourierSector i u) = realFourierSector i u :=
  realFourierSector_idempotent i u
example (i j : Fin 6) (hij : i ≠ j) (u : SpatialL2) :
    realFourierSector i (realFourierSector j u) = 0 := realFourierSector_comp_eq_zero hij u
example (u : SpatialL2) : ∑ i : Fin 6, realFourierSector i u = u :=
  sum_realFourierSector u
example (i : Fin 6) (u v : SpatialL2) :
    inner ℝ (realFourierSector i u) v = inner ℝ u (realFourierSector i v) :=
  inner_realFourierSector_left i u v
example (i j : Fin 6) (hij : i ≠ j) (u v : SpatialL2) :
    inner ℝ (realFourierSector i u) (realFourierSector j v) = 0 :=
  inner_realFourierSector_eq_zero hij u v
example (u : SpatialL2) : (∑ i : Fin 6, ‖realFourierSector i u‖ ^ 2) = ‖u‖ ^ 2 :=
  sum_norm_realFourierSector_sq u

end QFARealSectorL2.ExpectedTypes

-- Ordered, named full type and axiom reports; external verification only.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.hermitian_frequencySector"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.hermitian_frequencySector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.hermitian_frequencySector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.hermitian_frequencySector"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.hermitian_frequencySector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.hermitian_frequencySector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.conjugate_fourierSector_complexify"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.conjugate_fourierSector_complexify
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.conjugate_fourierSector_complexify"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.conjugate_fourierSector_complexify"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.conjugate_fourierSector_complexify
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.conjugate_fourierSector_complexify"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.complexify_realFourierSector"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.complexify_realFourierSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.complexify_realFourierSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.complexify_realFourierSector"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.complexify_realFourierSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.complexify_realFourierSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSectorCLM"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSectorCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSectorCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSectorCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSectorCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSectorCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSectorCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSectorCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSectorCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSectorCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSectorCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSectorCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_add"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_add
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_add"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_add
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_smul"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_smul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_smul"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_zero"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.norm_realFourierSector_le"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.norm_realFourierSector_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.norm_realFourierSector_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.norm_realFourierSector_le"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.norm_realFourierSector_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.norm_realFourierSector_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_idempotent"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_idempotent
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_idempotent"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_idempotent"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_idempotent
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_idempotent"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_comp_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_comp_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_comp_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_comp_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_comp_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.realFourierSector_comp_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.sum_realFourierSector"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.sum_realFourierSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.sum_realFourierSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.sum_realFourierSector"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.sum_realFourierSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.sum_realFourierSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.inner_realFourierSector_left"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.inner_realFourierSector_left
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.inner_realFourierSector_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.inner_realFourierSector_left"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.inner_realFourierSector_left
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.inner_realFourierSector_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.inner_realFourierSector_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.inner_realFourierSector_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.inner_realFourierSector_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.inner_realFourierSector_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.inner_realFourierSector_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.inner_realFourierSector_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.sum_norm_realFourierSector_sq"
#check @MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.sum_norm_realFourierSector_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.sum_norm_realFourierSector_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.sum_norm_realFourierSector_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.sum_norm_realFourierSector_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers.sum_norm_realFourierSector_sq"
