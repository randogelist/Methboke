import QFASixSectorL2.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section
open Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform

namespace QFASixSectorL2.ExpectedTypes
open QFA.Endpoints.Agmon (ComplexVector ComplexL2)
open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers

-- Full-volume Euclidean-vector L2, not scalar or finite-volume surrogates.
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl

-- The field is actually multiplied by the literal sector indicator.
example (i : Fin 6) (f : ComplexL2) : frequencySector i f =
    ((Lp.memLp f).indicator (measurableSet_sixSector i)).toLp
      ((sixSector i).indicator (fun ξ : Space => f ξ)) := rfl
example (i : Fin 6) (f : ComplexL2) :
    (fun ξ : Space => frequencySector i f ξ) =ᵐ[volume]
      (sixSector i).indicator (fun ξ : Space => f ξ) := frequencySector_ae i f
example (i : Fin 6) (f : ComplexL2) : ‖frequencySector i f‖ ≤ ‖f‖ :=
  norm_frequencySector_le i f
example (i : Fin 6) (f g : ComplexL2) :
    frequencySector i (f + g) = frequencySector i f + frequencySector i g :=
  frequencySector_add i f g
example (i : Fin 6) (c : ℂ) (f : ComplexL2) :
    frequencySector i (c • f) = c • frequencySector i f := frequencySector_smul i c f
example (i : Fin 6) : frequencySector i 0 = 0 := frequencySector_zero i
example (i : Fin 6) : ComplexL2 →L[ℂ] ComplexL2 := frequencySectorCLM i
example (i : Fin 6) (f : ComplexL2) : frequencySectorCLM i f =
    ((Lp.memLp f).indicator (measurableSet_sixSector i)).toLp
      ((sixSector i).indicator (fun ξ : Space => f ξ)) := rfl
example (i : Fin 6) (f : ComplexL2) : frequencySectorCLM i f = frequencySector i f :=
  frequencySectorCLM_apply i f
example (i : Fin 6) (f : ComplexL2) :
    frequencySector i (frequencySector i f) = frequencySector i f :=
  frequencySector_idempotent i f
example (i j : Fin 6) (hij : i ≠ j) (f : ComplexL2) :
    frequencySector i (frequencySector j f) = 0 := frequencySector_comp_eq_zero hij f
example (f : ComplexL2) : ∑ i : Fin 6, frequencySector i f = f :=
  sum_frequencySector f
example (i : Fin 6) (f g : ComplexL2) :
    inner ℂ (frequencySector i f) g = inner ℂ f (frequencySector i g) :=
  inner_frequencySector_left i f g
example (i j : Fin 6) (hij : i ≠ j) (f g : ComplexL2) :
    inner ℂ (frequencySector i f) (frequencySector j g) = 0 :=
  inner_frequencySector_eq_zero hij f g
example (f : ComplexL2) : (∑ i : Fin 6, ‖frequencySector i f‖ ^ 2) = ‖f‖ ^ 2 :=
  sum_norm_frequencySector_sq f

-- The conjugate uses Mathlib's actual L2 Fourier transform and inverse.
example (i : Fin 6) (f : ComplexL2) :
    fourierSector i f = 𝓕⁻ (frequencySector i (𝓕 f)) := rfl
example (i : Fin 6) (f : ComplexL2) :
    𝓕 (fourierSector i f) = frequencySector i (𝓕 f) := fourier_fourierSector i f
example (i : Fin 6) (f : ComplexL2) : ‖fourierSector i f‖ ≤ ‖f‖ :=
  norm_fourierSector_le i f
example (i : Fin 6) (f g : ComplexL2) :
    fourierSector i (f + g) = fourierSector i f + fourierSector i g :=
  fourierSector_add i f g
example (i : Fin 6) (c : ℂ) (f : ComplexL2) :
    fourierSector i (c • f) = c • fourierSector i f := fourierSector_smul i c f
example (i : Fin 6) : ComplexL2 →L[ℂ] ComplexL2 := fourierSectorCLM i
example (i : Fin 6) (f : ComplexL2) :
    fourierSectorCLM i f = 𝓕⁻ (frequencySector i (𝓕 f)) := rfl
example (i : Fin 6) (f : ComplexL2) : fourierSectorCLM i f = fourierSector i f :=
  fourierSectorCLM_apply i f
example (i : Fin 6) (f : ComplexL2) :
    fourierSector i (fourierSector i f) = fourierSector i f := fourierSector_idempotent i f
example (i j : Fin 6) (hij : i ≠ j) (f : ComplexL2) :
    fourierSector i (fourierSector j f) = 0 := fourierSector_comp_eq_zero hij f
example (f : ComplexL2) : ∑ i : Fin 6, fourierSector i f = f := sum_fourierSector f
example (i : Fin 6) (f g : ComplexL2) :
    inner ℂ (fourierSector i f) g = inner ℂ f (fourierSector i g) :=
  inner_fourierSector_left i f g
example (i j : Fin 6) (hij : i ≠ j) (f g : ComplexL2) :
    inner ℂ (fourierSector i f) (fourierSector j g) = 0 :=
  inner_fourierSector_eq_zero hij f g
example (f : ComplexL2) : (∑ i : Fin 6, ‖fourierSector i f‖ ^ 2) = ‖f‖ ^ 2 :=
  sum_norm_fourierSector_sq f

-- Both actual L2 witnesses are retained; this does not invent a derivative.
example (i : Fin 6) (f g : ComplexL2) (m : Space → ℂ)
    (h : (fun ξ : Space => g ξ) =ᵐ[volume] (fun ξ : Space => m ξ • f ξ)) :
    (fun ξ : Space => frequencySector i g ξ) =ᵐ[volume]
      (fun ξ : Space => m ξ • frequencySector i f ξ) :=
  frequencySector_multiplier_ae i f g m h

end QFASixSectorL2.ExpectedTypes

-- Named reports execute only in authorized external verification.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_ae"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.norm_frequencySector_le"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.norm_frequencySector_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.norm_frequencySector_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.norm_frequencySector_le"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.norm_frequencySector_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.norm_frequencySector_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_add"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_add
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_add"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_add
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_smul"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_smul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_smul"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_zero"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySectorCLM"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySectorCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySectorCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySectorCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySectorCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySectorCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySectorCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySectorCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySectorCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySectorCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySectorCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySectorCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_idempotent"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_idempotent
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_idempotent"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_idempotent"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_idempotent
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_idempotent"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_comp_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_comp_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_comp_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_comp_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_comp_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_comp_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_frequencySector"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_frequencySector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_frequencySector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_frequencySector"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_frequencySector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_frequencySector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_frequencySector_left"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_frequencySector_left
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_frequencySector_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_frequencySector_left"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_frequencySector_left
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_frequencySector_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_frequencySector_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_frequencySector_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_frequencySector_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_frequencySector_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_frequencySector_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_frequencySector_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_norm_frequencySector_sq"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_norm_frequencySector_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_norm_frequencySector_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_norm_frequencySector_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_norm_frequencySector_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_norm_frequencySector_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourier_fourierSector"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourier_fourierSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourier_fourierSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourier_fourierSector"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourier_fourierSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourier_fourierSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.norm_fourierSector_le"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.norm_fourierSector_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.norm_fourierSector_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.norm_fourierSector_le"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.norm_fourierSector_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.norm_fourierSector_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_add"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_add
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_add"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_add
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_smul"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_smul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_smul"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSectorCLM"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSectorCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSectorCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSectorCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSectorCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSectorCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSectorCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSectorCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSectorCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSectorCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSectorCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSectorCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_idempotent"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_idempotent
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_idempotent"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_idempotent"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_idempotent
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_idempotent"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_comp_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_comp_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_comp_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_comp_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_comp_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.fourierSector_comp_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_fourierSector"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_fourierSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_fourierSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_fourierSector"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_fourierSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_fourierSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_fourierSector_left"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_fourierSector_left
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_fourierSector_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_fourierSector_left"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_fourierSector_left
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_fourierSector_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_fourierSector_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_fourierSector_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_fourierSector_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_fourierSector_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_fourierSector_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.inner_fourierSector_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_norm_fourierSector_sq"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_norm_fourierSector_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_norm_fourierSector_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_norm_fourierSector_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_norm_fourierSector_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.sum_norm_fourierSector_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_multiplier_ae"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_multiplier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_multiplier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_multiplier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_multiplier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers.frequencySector_multiplier_ae"
