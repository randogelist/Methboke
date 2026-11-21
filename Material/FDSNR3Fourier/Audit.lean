import FDSNR3Fourier.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory SingularClosure Metric
open scoped BigOperators ContDiff FourierTransform SchwartzMap ComplexConjugate Topology
open LineDeriv
open MethbokeAddon.FDSNR3

noncomputable section

example (v : Vec) : complexifyCLM v = complexify v := by
  apply MethbokeAddon.FDSNR3.complexifyCLM_apply <;> assumption

example (v : Vec) : ‖complexify v‖ = ‖v‖ := by
  apply MethbokeAddon.FDSNR3.norm_complexify <;> assumption

example (f : 𝓢(Vec, Vec)) (x : Vec) :
    complexifySchwartz f x = complexify (f x) := by
  apply MethbokeAddon.FDSNR3.complexifySchwartz_apply <;> assumption

example (f : 𝓢(Vec, Vec)) :
    fourierVelocity f = ((𝓕 (complexifySchwartz f) : 𝓢(Vec, CVec)) : Vec → CVec) := by
  apply MethbokeAddon.FDSNR3.fourierVelocity_eq_schwartz <;> assumption

example (f : 𝓢(Vec, CVec)) :
    𝓕⁻ (𝓕 f) = f := by
  apply MethbokeAddon.FDSNR3.schwartz_fourierInv_fourier <;> assumption

example (f : 𝓢(Vec, CVec)) :
    𝓕 (𝓕⁻ f) = f := by
  apply MethbokeAddon.FDSNR3.schwartz_fourier_fourierInv <;> assumption

example (f : 𝓢(Vec, Vec)) (x : Vec) :
    realify (𝓕⁻ (fourierVelocity f) x) = f x := by
  apply MethbokeAddon.FDSNR3.physical_fourier_inversion <;> assumption

example :
    Function.Injective (𝓕 : 𝓢(Vec, CVec) → 𝓢(Vec, CVec)) := by
  apply MethbokeAddon.FDSNR3.schwartz_fourier_injective <;> assumption

example {f g : 𝓢(Vec, Vec)}
    (h : fourierVelocity f = fourierVelocity g) : f = g := by
  apply MethbokeAddon.FDSNR3.fourierVelocity_injective_on_schwartz <;> assumption

example (f : Vec → CVec) (ξ : Vec) :
    𝓕 f ξ = ∫ x : Vec,
      MethbokeAddon.FDSN.phase (-2 * Real.pi * inner ℝ x ξ) • f x := by
  apply MethbokeAddon.FDSNR3.fourier_eq_phase <;> assumption

example (f : Vec → ℂ) (ξ : Vec) :
    𝓕 f ξ = ∫ x : Vec,
      MethbokeAddon.FDSN.phase (-2 * Real.pi * inner ℝ x ξ) * f x := by
  apply MethbokeAddon.FDSNR3.scalar_fourier_eq_phase <;> assumption

example (L : CVec →L[ℂ] ℂ)
    {f : Vec → CVec} (hf : Integrable f) (ξ : Vec) :
    𝓕 (fun x => L (f x)) ξ = L (𝓕 f ξ) := by
  apply MethbokeAddon.FDSNR3.fourier_observation <;> assumption

example {f : Vec → CVec} (hf : Integrable f)
    (ξ : Vec) (i : Fin 3) :
    (𝓕 f ξ) i = 𝓕 (fun x => f x i) ξ := by
  apply MethbokeAddon.FDSNR3.fourier_coordinate <;> assumption

example (L : CVec →L[ℂ] ℂ)
    (f : 𝓢(Vec, CVec)) :
    𝓕 (SchwartzMap.postcompCLM L f) =
      SchwartzMap.postcompCLM L (𝓕 f) := by
  apply MethbokeAddon.FDSNR3.schwartz_fourier_observation <;> assumption

example (f : Vec → ℝ) (ξ : Vec) :
    𝓕 (fun x : Vec => (f x : ℂ)) (-ξ) =
      conj (𝓕 (fun x : Vec => (f x : ℂ)) ξ) := by
  apply MethbokeAddon.FDSNR3.scalar_fourier_real_conjugacy <;> assumption

example (f : 𝓢(Vec, Vec)) (ξ : Vec) (i : Fin 3) :
    fourierVelocity f (-ξ) i = conj (fourierVelocity f ξ i) := by
  apply MethbokeAddon.FDSNR3.fourierVelocity_conjugacy <;> assumption

example (f : Vec → ℂ) (ξ : Vec) :
    𝓕 (fun x : Vec => conj (f x)) (-ξ) = conj (𝓕 f ξ) := by
  apply MethbokeAddon.FDSNR3.scalar_fourier_conjugate_neg <;> assumption

example {f : Vec → CVec} (hf : Integrable f)
    (x : Vec) (i : Fin 3) :
    (𝓕⁻ f x) i = 𝓕⁻ (fun ξ => f ξ i) x := by
  apply MethbokeAddon.FDSNR3.fourierInv_coordinate <;> assumption

example (f : Vec → ℂ)
    (hf : ∀ ξ : Vec, f (-ξ) = conj (f ξ)) (x : Vec) :
    𝓕⁻ f x = conj (𝓕⁻ f x) := by
  apply MethbokeAddon.FDSNR3.scalar_fourierInv_fixedByConj <;> assumption

example (f : 𝓢(Vec, CVec))
    (hf : ∀ ξ : Vec, ∀ i : Fin 3, f (-ξ) i = conj (f ξ i)) (x : Vec) :
    complexify (realify (𝓕⁻ f x)) = 𝓕⁻ f x := by
  apply MethbokeAddon.FDSNR3.inverse_fourier_real_of_hermitian <;> assumption

example (f : Vec → CVec) (y ξ : Vec) :
    𝓕 (fun x : Vec => f (x + y)) ξ =
      MethbokeAddon.FDSN.phase (2 * Real.pi * inner ℝ y ξ) • 𝓕 f ξ := by
  apply MethbokeAddon.FDSNR3.fourier_translation <;> assumption

example (v : Field) (y ξ : Vec) :
    fourierVelocity (fun x => v (x + y)) ξ =
      MethbokeAddon.FDSN.phase (2 * Real.pi * inner ℝ y ξ) • fourierVelocity v ξ := by
  apply MethbokeAddon.FDSNR3.fourierVelocity_translation <;> assumption

example (f : 𝓢(Vec, CVec)) (m ξ : Vec) :
    𝓕 (fun x : Vec => fderiv ℝ (f : Vec → CVec) x m) ξ =
      (2 * (Real.pi : ℂ) * Complex.I) •
        ((inner ℝ ξ m) • 𝓕 f ξ) := by
  apply MethbokeAddon.FDSNR3.fourier_directionalDerivative <;> assumption

example (f : 𝓢(Vec, CVec)) (x : Vec) :
    schwartzDivergence f x =
      ∑ i : Fin 3, (fderiv ℝ (f : Vec → CVec) x (unitVector i)) i := by
  apply MethbokeAddon.FDSNR3.schwartzDivergence_apply <;> assumption

example (f : 𝓢(Vec, CVec)) (ξ : Vec) :
    𝓕 (schwartzDivergence f) ξ =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ∑ i : Fin 3, (ξ i : ℂ) * (𝓕 f ξ) i := by
  apply MethbokeAddon.FDSNR3.fourier_schwartzDivergence <;> assumption

example {v : Field} {x : Vec} (hv : DifferentiableAt ℝ v x) :
    fderiv ℝ (fun y => complexify (v y)) x =
      complexifyCLM.comp (fderiv ℝ v x) := by
  apply MethbokeAddon.FDSNR3.fderiv_complexify <;> assumption

example (f : 𝓢(Vec, Vec)) (x : Vec) :
    schwartzDivergence (complexifySchwartz f) x =
      (divergence (f : Field) x : ℂ) := by
  apply MethbokeAddon.FDSNR3.schwartzDivergence_complexify <;> assumption

example (f : 𝓢(Vec, Vec))
    (hf : ∀ x : Vec, divergence (f : Field) x = 0) (ξ : Vec) :
    ∑ i : Fin 3, (ξ i : ℂ) * fourierVelocity f ξ i = 0 := by
  apply MethbokeAddon.FDSNR3.fourierVelocity_divergence_free <;> assumption

example (f : 𝓢(Vec, CVec)) :
    (∫ ξ : Vec, ‖𝓕 f ξ‖ ^ 2) = ∫ x : Vec, ‖f x‖ ^ 2 := by
  apply MethbokeAddon.FDSNR3.schwartz_plancherel <;> assumption

example (f : 𝓢(Vec, Vec)) :
    (∫ ξ : Vec, ‖fourierVelocity f ξ‖ ^ 2) = ∫ x : Vec, ‖f x‖ ^ 2 := by
  apply MethbokeAddon.FDSNR3.physical_plancherel <;> assumption

example (v : Vec) (i : Fin 3) : complexifyCLM v i = (v i : ℂ) := rfl

example (f : 𝓢(Vec, Vec)) :
    complexifySchwartz f = SchwartzMap.postcompCLM complexifyCLM f := rfl

example (f : 𝓢(Vec, CVec)) :
    schwartzDivergence f =
      ∑ i : Fin 3, SchwartzMap.postcompCLM
        (EuclideanSpace.proj i : CVec →L[ℂ] ℂ) (∂_{unitVector i} f) := rfl

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexifyCLM"
#check @MethbokeAddon.FDSNR3.complexifyCLM
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexifyCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexifyCLM"
#print axioms MethbokeAddon.FDSNR3.complexifyCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexifyCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexifyCLM_apply"
#check @MethbokeAddon.FDSNR3.complexifyCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexifyCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexifyCLM_apply"
#print axioms MethbokeAddon.FDSNR3.complexifyCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexifyCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.norm_complexify"
#check @MethbokeAddon.FDSNR3.norm_complexify
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.norm_complexify"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.norm_complexify"
#print axioms MethbokeAddon.FDSNR3.norm_complexify
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.norm_complexify"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexifySchwartz"
#check @MethbokeAddon.FDSNR3.complexifySchwartz
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexifySchwartz"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexifySchwartz"
#print axioms MethbokeAddon.FDSNR3.complexifySchwartz
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexifySchwartz"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexifySchwartz_apply"
#check @MethbokeAddon.FDSNR3.complexifySchwartz_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexifySchwartz_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexifySchwartz_apply"
#print axioms MethbokeAddon.FDSNR3.complexifySchwartz_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexifySchwartz_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_eq_schwartz"
#check @MethbokeAddon.FDSNR3.fourierVelocity_eq_schwartz
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierVelocity_eq_schwartz"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_eq_schwartz"
#print axioms MethbokeAddon.FDSNR3.fourierVelocity_eq_schwartz
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierVelocity_eq_schwartz"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartz_fourierInv_fourier"
#check @MethbokeAddon.FDSNR3.schwartz_fourierInv_fourier
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartz_fourierInv_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartz_fourierInv_fourier"
#print axioms MethbokeAddon.FDSNR3.schwartz_fourierInv_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartz_fourierInv_fourier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartz_fourier_fourierInv"
#check @MethbokeAddon.FDSNR3.schwartz_fourier_fourierInv
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartz_fourier_fourierInv"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartz_fourier_fourierInv"
#print axioms MethbokeAddon.FDSNR3.schwartz_fourier_fourierInv
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartz_fourier_fourierInv"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physical_fourier_inversion"
#check @MethbokeAddon.FDSNR3.physical_fourier_inversion
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physical_fourier_inversion"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physical_fourier_inversion"
#print axioms MethbokeAddon.FDSNR3.physical_fourier_inversion
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physical_fourier_inversion"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartz_fourier_injective"
#check @MethbokeAddon.FDSNR3.schwartz_fourier_injective
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartz_fourier_injective"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartz_fourier_injective"
#print axioms MethbokeAddon.FDSNR3.schwartz_fourier_injective
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartz_fourier_injective"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_injective_on_schwartz"
#check @MethbokeAddon.FDSNR3.fourierVelocity_injective_on_schwartz
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierVelocity_injective_on_schwartz"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_injective_on_schwartz"
#print axioms MethbokeAddon.FDSNR3.fourierVelocity_injective_on_schwartz
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierVelocity_injective_on_schwartz"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourier_eq_phase"
#check @MethbokeAddon.FDSNR3.fourier_eq_phase
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourier_eq_phase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourier_eq_phase"
#print axioms MethbokeAddon.FDSNR3.fourier_eq_phase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourier_eq_phase"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.scalar_fourier_eq_phase"
#check @MethbokeAddon.FDSNR3.scalar_fourier_eq_phase
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.scalar_fourier_eq_phase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.scalar_fourier_eq_phase"
#print axioms MethbokeAddon.FDSNR3.scalar_fourier_eq_phase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.scalar_fourier_eq_phase"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourier_observation"
#check @MethbokeAddon.FDSNR3.fourier_observation
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourier_observation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourier_observation"
#print axioms MethbokeAddon.FDSNR3.fourier_observation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourier_observation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourier_coordinate"
#check @MethbokeAddon.FDSNR3.fourier_coordinate
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourier_coordinate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourier_coordinate"
#print axioms MethbokeAddon.FDSNR3.fourier_coordinate
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourier_coordinate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartz_fourier_observation"
#check @MethbokeAddon.FDSNR3.schwartz_fourier_observation
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartz_fourier_observation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartz_fourier_observation"
#print axioms MethbokeAddon.FDSNR3.schwartz_fourier_observation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartz_fourier_observation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.scalar_fourier_real_conjugacy"
#check @MethbokeAddon.FDSNR3.scalar_fourier_real_conjugacy
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.scalar_fourier_real_conjugacy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.scalar_fourier_real_conjugacy"
#print axioms MethbokeAddon.FDSNR3.scalar_fourier_real_conjugacy
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.scalar_fourier_real_conjugacy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_conjugacy"
#check @MethbokeAddon.FDSNR3.fourierVelocity_conjugacy
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierVelocity_conjugacy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_conjugacy"
#print axioms MethbokeAddon.FDSNR3.fourierVelocity_conjugacy
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierVelocity_conjugacy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.scalar_fourier_conjugate_neg"
#check @MethbokeAddon.FDSNR3.scalar_fourier_conjugate_neg
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.scalar_fourier_conjugate_neg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.scalar_fourier_conjugate_neg"
#print axioms MethbokeAddon.FDSNR3.scalar_fourier_conjugate_neg
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.scalar_fourier_conjugate_neg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierInv_coordinate"
#check @MethbokeAddon.FDSNR3.fourierInv_coordinate
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierInv_coordinate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierInv_coordinate"
#print axioms MethbokeAddon.FDSNR3.fourierInv_coordinate
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierInv_coordinate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.scalar_fourierInv_fixedByConj"
#check @MethbokeAddon.FDSNR3.scalar_fourierInv_fixedByConj
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.scalar_fourierInv_fixedByConj"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.scalar_fourierInv_fixedByConj"
#print axioms MethbokeAddon.FDSNR3.scalar_fourierInv_fixedByConj
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.scalar_fourierInv_fixedByConj"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.inverse_fourier_real_of_hermitian"
#check @MethbokeAddon.FDSNR3.inverse_fourier_real_of_hermitian
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.inverse_fourier_real_of_hermitian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.inverse_fourier_real_of_hermitian"
#print axioms MethbokeAddon.FDSNR3.inverse_fourier_real_of_hermitian
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.inverse_fourier_real_of_hermitian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourier_translation"
#check @MethbokeAddon.FDSNR3.fourier_translation
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourier_translation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourier_translation"
#print axioms MethbokeAddon.FDSNR3.fourier_translation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourier_translation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_translation"
#check @MethbokeAddon.FDSNR3.fourierVelocity_translation
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierVelocity_translation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_translation"
#print axioms MethbokeAddon.FDSNR3.fourierVelocity_translation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierVelocity_translation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourier_directionalDerivative"
#check @MethbokeAddon.FDSNR3.fourier_directionalDerivative
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourier_directionalDerivative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourier_directionalDerivative"
#print axioms MethbokeAddon.FDSNR3.fourier_directionalDerivative
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourier_directionalDerivative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzDivergence"
#check @MethbokeAddon.FDSNR3.schwartzDivergence
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzDivergence"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzDivergence"
#print axioms MethbokeAddon.FDSNR3.schwartzDivergence
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzDivergence"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzDivergence_apply"
#check @MethbokeAddon.FDSNR3.schwartzDivergence_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzDivergence_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzDivergence_apply"
#print axioms MethbokeAddon.FDSNR3.schwartzDivergence_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzDivergence_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourier_schwartzDivergence"
#check @MethbokeAddon.FDSNR3.fourier_schwartzDivergence
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourier_schwartzDivergence"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourier_schwartzDivergence"
#print axioms MethbokeAddon.FDSNR3.fourier_schwartzDivergence
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourier_schwartzDivergence"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fderiv_complexify"
#check @MethbokeAddon.FDSNR3.fderiv_complexify
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fderiv_complexify"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fderiv_complexify"
#print axioms MethbokeAddon.FDSNR3.fderiv_complexify
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fderiv_complexify"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzDivergence_complexify"
#check @MethbokeAddon.FDSNR3.schwartzDivergence_complexify
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzDivergence_complexify"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzDivergence_complexify"
#print axioms MethbokeAddon.FDSNR3.schwartzDivergence_complexify
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzDivergence_complexify"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_divergence_free"
#check @MethbokeAddon.FDSNR3.fourierVelocity_divergence_free
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierVelocity_divergence_free"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_divergence_free"
#print axioms MethbokeAddon.FDSNR3.fourierVelocity_divergence_free
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierVelocity_divergence_free"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartz_plancherel"
#check @MethbokeAddon.FDSNR3.schwartz_plancherel
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartz_plancherel"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartz_plancherel"
#print axioms MethbokeAddon.FDSNR3.schwartz_plancherel
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartz_plancherel"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physical_plancherel"
#check @MethbokeAddon.FDSNR3.physical_plancherel
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physical_plancherel"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physical_plancherel"
#print axioms MethbokeAddon.FDSNR3.physical_plancherel
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physical_plancherel"

