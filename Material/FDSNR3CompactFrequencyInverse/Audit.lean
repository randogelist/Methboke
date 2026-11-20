import FDSNR3CompactFrequencyInverse.Endpoint

set_option pp.universes true
set_option pp.fullNames true

set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory SingularClosure MethbokeAddon.FDSNR3
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology

section SliceDefinitions
variable (P X : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

example : rightSliceCLM P X =
    (0 : X →L[ℝ] P).prod (ContinuousLinearMap.id ℝ X) := rfl

example (p : P) : (rightSliceAffine P X p : X → P × X) =
    (fun x : X => (p, x)) := rfl

variable {P X}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
example (A : 𝓢(P × X, E)) (p : P) :
    (schwartzRightSlice A p : X → E) = (fun x : X => A (p, x)) := rfl
end SliceDefinitions

section FourierDefinitions
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

example : parameterProjectionCLM P =
    (ContinuousLinearMap.fst ℝ P Vec).prod (0 : (P × Vec) →L[ℝ] Vec) := rfl

example : frequencyPairingCLM P =
    ((ContinuousLinearMap.compL ℝ (P × Vec) Vec ℝ).flip
      (ContinuousLinearMap.snd ℝ P Vec)).comp
        ((innerSL ℝ).comp (ContinuousLinearMap.snd ℝ P Vec)) := rfl

example (A : 𝓢(P × Vec, E)) : partialFourierJetStep A =
    SchwartzMap.postcompCLM
      ((ContinuousLinearMap.compL ℝ (P × Vec) (P × Vec) E).flip (parameterProjectionCLM P))
      (SchwartzMap.fderivCLM ℝ (P × Vec) E A) +
    (-(2 * (Real.pi : ℂ) * Complex.I)) •
      SchwartzMap.smulRightCLM ℝ E (frequencyPairingCLM P) A := rfl

example (A : 𝓢(P × Vec, E)) : partialFourierJet A 0 =
    SchwartzMap.postcompCLM
      (continuousMultilinearCurryFin0 ℝ (P × Vec) E).symm.toContinuousLinearEquiv.toContinuousLinearMap A := rfl

example (A : 𝓢(P × Vec, E)) (n : ℕ) : partialFourierJet A (n + 1) =
    SchwartzMap.postcompCLM
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => P × Vec) E).symm.toContinuousLinearEquiv.toContinuousLinearMap
      (partialFourierJetStep (partialFourierJet A n)) := rfl

example (A : 𝓢(P × Vec, E)) (ξ : Vec) (q : P × Vec) :
    partialFourierTaylor A ξ q = (fun n =>
      Real.fourierChar (-inner ℝ ξ q.2) • partialFourierJet A n (q.1, ξ)) := rfl

example (A : 𝓢(P × Vec, E)) : partialFourierTransform A =
    (fun q : P × Vec => 𝓕 (fun ξ : Vec => A (q.1, ξ)) q.2) := rfl

example (A : 𝓢(P × Vec, E)) : (partialFourierSchwartz A : P × Vec → E) =
    (fun q : P × Vec => 𝓕 (fun ξ : Vec => A (q.1, ξ)) q.2) := rfl

example : (frequencyReflection P : P × Vec → P × Vec) =
    (fun q : P × Vec => (q.1, -q.2)) := rfl

example (A : 𝓢(P × Vec, E)) : (partialFourierInverse A : P × Vec → E) =
    (fun q : P × Vec => 𝓕 (fun ξ : Vec => A (q.1, ξ)) (-q.2)) := rfl
end FourierDefinitions

example {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (x : X) :
    rightSliceCLM P X x = (0, x) := by
  apply @rightSliceCLM_apply <;> assumption

example {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (p : P) (x : X) :
    rightSliceAffine P X p x = (p, x) := by
  apply @rightSliceAffine_apply <;> assumption

example {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (p : P) :
    (rightSliceAffine P X p).contLinear = rightSliceCLM P X := by
  apply @rightSliceAffine_contLinear <;> assumption

example {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : 𝓢(P × X, E)) (p : P) (x : X) :
    schwartzRightSlice A p x = A (p, x) := by
  apply @schwartzRightSlice_apply <;> assumption

example {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : 𝓢(P × X, E)) (p : P) :
    (schwartzRightSlice A p : X → E) = fun x : X => A (p, x) := by
  apply @schwartzRightSlice_coe <;> assumption

example {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : 𝓢(P × X, E))
    (p : P) (n : ℕ) (x : X) :
    iteratedFDeriv ℝ n (schwartzRightSlice A p) x =
      (iteratedFDeriv ℝ n A (p, x)).compContinuousLinearMap
        (fun _ : Fin n => rightSliceCLM P X) := by
  apply @iteratedFDeriv_schwartzRightSlice <;> assumption

example {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : 𝓢(P × X, E))
    (p : P) (n : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ n (schwartzRightSlice A p) x‖ ≤
      ‖iteratedFDeriv ℝ n A (p, x)‖ * ‖rightSliceCLM P X‖ ^ n := by
  apply @norm_iteratedFDeriv_schwartzRightSlice_le <;> assumption

example {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : 𝓢(P × X, E))
    (a b n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P, ∀ x : X,
      (1 + ‖p‖) ^ a * (1 + ‖x‖) ^ b *
        ‖iteratedFDeriv ℝ n (schwartzRightSlice A p) x‖ ≤ C := by
  apply @schwartzRightSlice_uniform_weighted_jets <;> assumption

example {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : 𝓢(P × X, E)) (a k n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P, ∀ x : X,
      ‖p‖ ^ a * ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (schwartzRightSlice A p) x‖ ≤
        C * (1 + ‖x‖) ^ (-(m : ℝ)) := by
  apply @schwartzRightSlice_uniform_decay <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E)) (a k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P,
      ‖p‖ ^ a * (∫ ξ : Vec, ‖ξ‖ ^ k *
        ‖iteratedFDeriv ℝ n (schwartzRightSlice A p) ξ‖) ≤ C := by
  apply @schwartzFrequencySlice_uniform_integrals <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E)) :
    ∃ B : Vec → ℝ, Integrable B ∧ ∀ p : P, ∀ ξ : Vec, ‖A (p, ξ)‖ ≤ B ξ := by
  apply @schwartzFrequencySlice_dominated <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (q : P × Vec) :
    parameterProjectionCLM P q = (q.1, 0) := by
  apply @parameterProjectionCLM_apply <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (z q : P × Vec) :
    frequencyPairingCLM P z q = inner ℝ z.2 q.2 := by
  apply @frequencyPairingCLM_apply <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E)) (z q : P × Vec) :
    partialFourierJetStep A z q =
      fderiv ℝ A z (q.1, 0) +
        (-(2 * (Real.pi : ℂ) * Complex.I)) • ((inner ℝ z.2 q.2) • A z) := by
  apply @partialFourierJetStep_apply <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E)) (z : P × Vec)
    (m : Fin 0 → P × Vec) :
    partialFourierJet A 0 z m = A z := by
  apply @partialFourierJet_zero_apply <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E)) (n : ℕ)
    (z : P × Vec) (m : Fin (n + 1) → P × Vec) :
    partialFourierJet A (n + 1) z m =
      partialFourierJetStep (partialFourierJet A n) z (m 0) (Fin.tail m) := by
  apply @partialFourierJet_succ_apply <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E))
    (ξ : Vec) (n : ℕ) (q : P × Vec) :
    HasFDerivAt (fun y => partialFourierTaylor A ξ y n)
      (partialFourierTaylor A ξ q (n + 1)).curryLeft q := by
  apply @partialFourierTaylor_hasFDerivAt <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E)) (ξ : Vec) :
    HasFTaylorSeriesUpToOn ∞
      (fun q : P × Vec => Real.fourierChar (-inner ℝ ξ q.2) • A (q.1, ξ))
      (partialFourierTaylor A ξ) univ := by
  apply @partialFourierTaylor_isTaylor <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E)) :
    HasFTaylorSeriesUpToOn ∞ (partialFourierTransform A)
      (fun q n => ∫ ξ : Vec, partialFourierTaylor A ξ q n) univ := by
  apply @partialFourierTransform_hasTaylor <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E)) :
    ContDiff ℝ ∞ (partialFourierTransform A) := by
  apply @partialFourierTransform_smooth <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E))
    (n : ℕ) (q : P × Vec) :
    iteratedFDeriv ℝ n (partialFourierTransform A) q =
      𝓕 (fun ξ : Vec => partialFourierJet A n (q.1, ξ)) q.2 := by
  apply @partialFourierTransform_iteratedFDeriv <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P, ∀ x : Vec,
      ‖p‖ ^ N * ‖𝓕 (fun ξ : Vec => A (p, ξ)) x‖ ≤ C := by
  apply @partialFourierTransform_parameter_weight <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P, ∀ x : Vec,
      ‖x‖ ^ N * ‖𝓕 (fun ξ : Vec => A (p, ξ)) x‖ ≤ C := by
  apply @partialFourierTransform_spatial_weight <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E)) (N n : ℕ) :
    ∃ C : ℝ, ∀ q : P × Vec,
      ‖q‖ ^ N * ‖iteratedFDeriv ℝ n (partialFourierTransform A) q‖ ≤ C := by
  apply @partialFourierTransform_decay <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E)) (p : P) (x : Vec) :
    partialFourierSchwartz A (p, x) = 𝓕 (fun ξ : Vec => A (p, ξ)) x := by
  apply @partialFourierSchwartz_apply <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (p : P) (x : Vec) :
    frequencyReflection P (p, x) = (p, -x) := by
  apply @frequencyReflection_apply <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E)) (p : P) (x : Vec) :
    partialFourierInverse A (p, x) = 𝓕⁻ (fun ξ : Vec => A (p, ξ)) x := by
  apply @partialFourierInverse_apply <;> assumption

example {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : 𝓢(P × Vec, E)) {p : P}
    (hp : ∀ ξ : Vec, A (p, ξ) = 0) (x : Vec) :
    partialFourierInverse A (p, x) = 0 := by
  apply @partialFourierInverse_zero_fiber <;> assumption

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.rightSliceCLM"
#check @MethbokeAddon.FDSNR3.rightSliceCLM
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.rightSliceCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.rightSliceCLM"
#print axioms MethbokeAddon.FDSNR3.rightSliceCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.rightSliceCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.rightSliceCLM_apply"
#check @MethbokeAddon.FDSNR3.rightSliceCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.rightSliceCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.rightSliceCLM_apply"
#print axioms MethbokeAddon.FDSNR3.rightSliceCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.rightSliceCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.rightSliceAffine"
#check @MethbokeAddon.FDSNR3.rightSliceAffine
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.rightSliceAffine"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.rightSliceAffine"
#print axioms MethbokeAddon.FDSNR3.rightSliceAffine
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.rightSliceAffine"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.rightSliceAffine_apply"
#check @MethbokeAddon.FDSNR3.rightSliceAffine_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.rightSliceAffine_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.rightSliceAffine_apply"
#print axioms MethbokeAddon.FDSNR3.rightSliceAffine_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.rightSliceAffine_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.rightSliceAffine_contLinear"
#check @MethbokeAddon.FDSNR3.rightSliceAffine_contLinear
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.rightSliceAffine_contLinear"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.rightSliceAffine_contLinear"
#print axioms MethbokeAddon.FDSNR3.rightSliceAffine_contLinear
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.rightSliceAffine_contLinear"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzRightSlice"
#check @MethbokeAddon.FDSNR3.schwartzRightSlice
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzRightSlice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzRightSlice"
#print axioms MethbokeAddon.FDSNR3.schwartzRightSlice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzRightSlice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzRightSlice_apply"
#check @MethbokeAddon.FDSNR3.schwartzRightSlice_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzRightSlice_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzRightSlice_apply"
#print axioms MethbokeAddon.FDSNR3.schwartzRightSlice_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzRightSlice_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzRightSlice_coe"
#check @MethbokeAddon.FDSNR3.schwartzRightSlice_coe
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzRightSlice_coe"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzRightSlice_coe"
#print axioms MethbokeAddon.FDSNR3.schwartzRightSlice_coe
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzRightSlice_coe"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.iteratedFDeriv_schwartzRightSlice"
#check @MethbokeAddon.FDSNR3.iteratedFDeriv_schwartzRightSlice
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.iteratedFDeriv_schwartzRightSlice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.iteratedFDeriv_schwartzRightSlice"
#print axioms MethbokeAddon.FDSNR3.iteratedFDeriv_schwartzRightSlice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.iteratedFDeriv_schwartzRightSlice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.norm_iteratedFDeriv_schwartzRightSlice_le"
#check @MethbokeAddon.FDSNR3.norm_iteratedFDeriv_schwartzRightSlice_le
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.norm_iteratedFDeriv_schwartzRightSlice_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.norm_iteratedFDeriv_schwartzRightSlice_le"
#print axioms MethbokeAddon.FDSNR3.norm_iteratedFDeriv_schwartzRightSlice_le
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.norm_iteratedFDeriv_schwartzRightSlice_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzRightSlice_uniform_weighted_jets"
#check @MethbokeAddon.FDSNR3.schwartzRightSlice_uniform_weighted_jets
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzRightSlice_uniform_weighted_jets"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzRightSlice_uniform_weighted_jets"
#print axioms MethbokeAddon.FDSNR3.schwartzRightSlice_uniform_weighted_jets
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzRightSlice_uniform_weighted_jets"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzRightSlice_uniform_decay"
#check @MethbokeAddon.FDSNR3.schwartzRightSlice_uniform_decay
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzRightSlice_uniform_decay"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzRightSlice_uniform_decay"
#print axioms MethbokeAddon.FDSNR3.schwartzRightSlice_uniform_decay
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzRightSlice_uniform_decay"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzFrequencySlice_uniform_integrals"
#check @MethbokeAddon.FDSNR3.schwartzFrequencySlice_uniform_integrals
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzFrequencySlice_uniform_integrals"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzFrequencySlice_uniform_integrals"
#print axioms MethbokeAddon.FDSNR3.schwartzFrequencySlice_uniform_integrals
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzFrequencySlice_uniform_integrals"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzFrequencySlice_dominated"
#check @MethbokeAddon.FDSNR3.schwartzFrequencySlice_dominated
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzFrequencySlice_dominated"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzFrequencySlice_dominated"
#print axioms MethbokeAddon.FDSNR3.schwartzFrequencySlice_dominated
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzFrequencySlice_dominated"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.parameterProjectionCLM"
#check @MethbokeAddon.FDSNR3.parameterProjectionCLM
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.parameterProjectionCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.parameterProjectionCLM"
#print axioms MethbokeAddon.FDSNR3.parameterProjectionCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.parameterProjectionCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.parameterProjectionCLM_apply"
#check @MethbokeAddon.FDSNR3.parameterProjectionCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.parameterProjectionCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.parameterProjectionCLM_apply"
#print axioms MethbokeAddon.FDSNR3.parameterProjectionCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.parameterProjectionCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.frequencyPairingCLM"
#check @MethbokeAddon.FDSNR3.frequencyPairingCLM
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.frequencyPairingCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.frequencyPairingCLM"
#print axioms MethbokeAddon.FDSNR3.frequencyPairingCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.frequencyPairingCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.frequencyPairingCLM_apply"
#check @MethbokeAddon.FDSNR3.frequencyPairingCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.frequencyPairingCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.frequencyPairingCLM_apply"
#print axioms MethbokeAddon.FDSNR3.frequencyPairingCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.frequencyPairingCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierJetStep"
#check @MethbokeAddon.FDSNR3.partialFourierJetStep
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierJetStep"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierJetStep"
#print axioms MethbokeAddon.FDSNR3.partialFourierJetStep
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierJetStep"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierJetStep_apply"
#check @MethbokeAddon.FDSNR3.partialFourierJetStep_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierJetStep_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierJetStep_apply"
#print axioms MethbokeAddon.FDSNR3.partialFourierJetStep_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierJetStep_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierJet"
#check @MethbokeAddon.FDSNR3.partialFourierJet
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierJet"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierJet"
#print axioms MethbokeAddon.FDSNR3.partialFourierJet
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierJet"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierJet_zero_apply"
#check @MethbokeAddon.FDSNR3.partialFourierJet_zero_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierJet_zero_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierJet_zero_apply"
#print axioms MethbokeAddon.FDSNR3.partialFourierJet_zero_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierJet_zero_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierJet_succ_apply"
#check @MethbokeAddon.FDSNR3.partialFourierJet_succ_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierJet_succ_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierJet_succ_apply"
#print axioms MethbokeAddon.FDSNR3.partialFourierJet_succ_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierJet_succ_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierTaylor"
#check @MethbokeAddon.FDSNR3.partialFourierTaylor
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierTaylor"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierTaylor"
#print axioms MethbokeAddon.FDSNR3.partialFourierTaylor
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierTaylor"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierTaylor_hasFDerivAt"
#check @MethbokeAddon.FDSNR3.partialFourierTaylor_hasFDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierTaylor_hasFDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierTaylor_hasFDerivAt"
#print axioms MethbokeAddon.FDSNR3.partialFourierTaylor_hasFDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierTaylor_hasFDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierTaylor_isTaylor"
#check @MethbokeAddon.FDSNR3.partialFourierTaylor_isTaylor
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierTaylor_isTaylor"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierTaylor_isTaylor"
#print axioms MethbokeAddon.FDSNR3.partialFourierTaylor_isTaylor
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierTaylor_isTaylor"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierTransform"
#check @MethbokeAddon.FDSNR3.partialFourierTransform
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierTransform"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierTransform"
#print axioms MethbokeAddon.FDSNR3.partialFourierTransform
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierTransform"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierTransform_hasTaylor"
#check @MethbokeAddon.FDSNR3.partialFourierTransform_hasTaylor
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierTransform_hasTaylor"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierTransform_hasTaylor"
#print axioms MethbokeAddon.FDSNR3.partialFourierTransform_hasTaylor
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierTransform_hasTaylor"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierTransform_smooth"
#check @MethbokeAddon.FDSNR3.partialFourierTransform_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierTransform_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierTransform_smooth"
#print axioms MethbokeAddon.FDSNR3.partialFourierTransform_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierTransform_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierTransform_iteratedFDeriv"
#check @MethbokeAddon.FDSNR3.partialFourierTransform_iteratedFDeriv
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierTransform_iteratedFDeriv"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierTransform_iteratedFDeriv"
#print axioms MethbokeAddon.FDSNR3.partialFourierTransform_iteratedFDeriv
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierTransform_iteratedFDeriv"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierTransform_parameter_weight"
#check @MethbokeAddon.FDSNR3.partialFourierTransform_parameter_weight
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierTransform_parameter_weight"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierTransform_parameter_weight"
#print axioms MethbokeAddon.FDSNR3.partialFourierTransform_parameter_weight
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierTransform_parameter_weight"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierTransform_spatial_weight"
#check @MethbokeAddon.FDSNR3.partialFourierTransform_spatial_weight
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierTransform_spatial_weight"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierTransform_spatial_weight"
#print axioms MethbokeAddon.FDSNR3.partialFourierTransform_spatial_weight
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierTransform_spatial_weight"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierTransform_decay"
#check @MethbokeAddon.FDSNR3.partialFourierTransform_decay
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierTransform_decay"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierTransform_decay"
#print axioms MethbokeAddon.FDSNR3.partialFourierTransform_decay
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierTransform_decay"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierSchwartz"
#check @MethbokeAddon.FDSNR3.partialFourierSchwartz
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierSchwartz"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierSchwartz"
#print axioms MethbokeAddon.FDSNR3.partialFourierSchwartz
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierSchwartz"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierSchwartz_apply"
#check @MethbokeAddon.FDSNR3.partialFourierSchwartz_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierSchwartz_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierSchwartz_apply"
#print axioms MethbokeAddon.FDSNR3.partialFourierSchwartz_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierSchwartz_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.frequencyReflection"
#check @MethbokeAddon.FDSNR3.frequencyReflection
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.frequencyReflection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.frequencyReflection"
#print axioms MethbokeAddon.FDSNR3.frequencyReflection
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.frequencyReflection"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.frequencyReflection_apply"
#check @MethbokeAddon.FDSNR3.frequencyReflection_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.frequencyReflection_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.frequencyReflection_apply"
#print axioms MethbokeAddon.FDSNR3.frequencyReflection_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.frequencyReflection_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierInverse"
#check @MethbokeAddon.FDSNR3.partialFourierInverse
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierInverse"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierInverse"
#print axioms MethbokeAddon.FDSNR3.partialFourierInverse
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierInverse"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierInverse_apply"
#check @MethbokeAddon.FDSNR3.partialFourierInverse_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierInverse_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierInverse_apply"
#print axioms MethbokeAddon.FDSNR3.partialFourierInverse_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierInverse_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.partialFourierInverse_zero_fiber"
#check @MethbokeAddon.FDSNR3.partialFourierInverse_zero_fiber
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.partialFourierInverse_zero_fiber"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.partialFourierInverse_zero_fiber"
#print axioms MethbokeAddon.FDSNR3.partialFourierInverse_zero_fiber
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.partialFourierInverse_zero_fiber"

