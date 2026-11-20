import FDSNR3Helical.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section
open SingularClosure MethbokeAddon.FDSNR3
open scoped BigOperators ComplexConjugate

example : (frequencyDot : Vec → CVec → ℂ) =
    (fun ξ z => ∑ i : Fin 3, (ξ i : ℂ) * z i) := rfl

example (ξ : Vec) :
    ((transverseLinearMap ξ : CVec →ₗ[ℂ] CVec) : CVec → CVec) =
      (fun z => z -
        ((∑ i : Fin 3, (ξ i : ℂ) * z i) / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) • complexify ξ) := rfl

example (ξ : Vec) :
    ((complexCrossLinearMap ξ : CVec →ₗ[ℂ] CVec) : CVec → CVec) =
      (fun z => WithLp.toLp 2
        (crossProduct (fun i : Fin 3 => (ξ i : ℂ)) (fun i => z i))) := rfl

example (σ : Fin 2) (ξ : Vec) :
    ((helicalLinearMap σ ξ : CVec →ₗ[ℂ] CVec) : CVec → CVec) =
      (fun z => (1 / 2 : ℂ) • (transverseSymbol ξ z +
        (((helicitySign σ : ℝ) : ℂ) * Complex.I / (‖ξ‖ : ℂ)) • complexCross ξ z)) := rfl

example : (helicityOperator : Vec → CVec → CVec) =
    (fun ξ z => (Complex.I / (‖ξ‖ : ℂ)) • complexCross ξ z) := rfl

example : ∀ (ξ : Vec) (z w : CVec),
    frequencyDot ξ (z + w) = frequencyDot ξ z + frequencyDot ξ w :=
  @frequencyDot_add

example : ∀ (ξ : Vec) (a : ℂ) (z : CVec),
    frequencyDot ξ (a • z) = a * frequencyDot ξ z :=
  @frequencyDot_smul

example : ∀ (ξ : Vec) (z w : CVec),
    frequencyDot ξ (z - w) = frequencyDot ξ z - frequencyDot ξ w :=
  @frequencyDot_sub

example : ∀ (ξ : Vec),
    frequencyDot ξ (complexify ξ) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) :=
  @frequencyDot_complexify

example : ∀ (ξ : Vec) (z : CVec),
    frequencyDot ξ z = inner ℂ (complexify ξ) z :=
  @frequencyDot_eq_inner

example : ∀ (ξ : Vec) (z : CVec),
    transverseSymbol ξ z =
      z - (frequencyDot ξ z / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) • complexify ξ :=
  @transverseSymbol_eq

example : ∀ (ξ : Vec) (z w : CVec),
    transverseSymbol ξ (z + w) =
      transverseSymbol ξ z + transverseSymbol ξ w :=
  @transverseSymbol_add

example : ∀ (ξ : Vec) (a : ℂ) (z : CVec),
    transverseSymbol ξ (a • z) = a • transverseSymbol ξ z :=
  @transverseSymbol_smul

example : ∀ (ξ : Vec) (z w : CVec),
    complexCross ξ (z + w) = complexCross ξ z + complexCross ξ w :=
  @complexCross_add

example : ∀ (ξ : Vec) (a : ℂ) (z : CVec),
    complexCross ξ (a • z) = a • complexCross ξ z :=
  @complexCross_smul

example : ∀ (ξ : Vec) (z w : CVec),
    complexCross ξ (z - w) = complexCross ξ z - complexCross ξ w :=
  @complexCross_sub

example : ∀ (σ : Fin 2) (ξ : Vec) (z w : CVec),
    helicalSymbol σ ξ (z + w) =
      helicalSymbol σ ξ z + helicalSymbol σ ξ w :=
  @helicalSymbol_add

example : ∀ (σ : Fin 2) (ξ : Vec) (a : ℂ) (z : CVec),
    helicalSymbol σ ξ (a • z) = a • helicalSymbol σ ξ z :=
  @helicalSymbol_smul

example : ∀ (σ : Fin 2) (ξ : Vec) (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (lam t : ℝ) (c : Vec → CVec),
    helicalSymbol σ ξ (packetRotate β ψ lam t c ξ) =
      packetPhase β ψ lam t ξ • helicalSymbol σ ξ (c ξ) :=
  @helicalSymbol_packetRotate

example : ∀ (σ : Fin 2) (ξ : Vec) (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (lam t : ℝ) (c : Vec → CVec),
    ‖helicalSymbol σ ξ (packetRotate β ψ lam t c ξ)‖ =
      ‖helicalSymbol σ ξ (c ξ)‖ :=
  @norm_helicalSymbol_packetRotate

example : ∀ (σ : Fin 2) (u v : Field) (ξ : Vec) (theta : ℝ)
    (h : fourierVelocity v ξ = MethbokeAddon.FDSN.phase theta • fourierVelocity u ξ),
    helicalPower σ v ξ = helicalPower σ u ξ :=
  @helicalPower_eq_of_fourier_phase

example : ∀ {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec),
    frequencyDot ξ (transverseSymbol ξ z) = 0 :=
  @frequencyDot_transverseSymbol

example : ∀ (ξ : Vec) {z : CVec} (hz : frequencyDot ξ z = 0),
    transverseSymbol ξ z = z :=
  @transverseSymbol_of_frequencyDot_eq_zero

example : ∀ {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec),
    transverseSymbol ξ (transverseSymbol ξ z) = transverseSymbol ξ z :=
  @transverseSymbol_idempotent

example : ∀ (ξ : Vec),
    complexCross ξ (complexify ξ) = 0 :=
  @complexCross_complexify

example : ∀ (ξ : Vec) (z : CVec),
    frequencyDot ξ (complexCross ξ z) = 0 :=
  @frequencyDot_complexCross

example : ∀ (ξ : Vec) (z : CVec),
    transverseSymbol ξ (complexCross ξ z) = complexCross ξ z :=
  @transverseSymbol_complexCross

example : ∀ (ξ : Vec) (z : CVec),
    complexCross ξ (transverseSymbol ξ z) = complexCross ξ z :=
  @complexCross_transverseSymbol

example : ∀ (ξ : Vec) (z : CVec),
    complexCross ξ (complexCross ξ z) =
      frequencyDot ξ z • complexify ξ - ((‖ξ‖ ^ 2 : ℝ) : ℂ) • z :=
  @complexCross_twice

example : ∀ (ξ : Vec) (z w : CVec),
    helicityOperator ξ (z + w) = helicityOperator ξ z + helicityOperator ξ w :=
  @helicityOperator_add

example : ∀ (ξ : Vec) (a : ℂ) (z : CVec),
    helicityOperator ξ (a • z) = a • helicityOperator ξ z :=
  @helicityOperator_smul

example : ∀ (σ : Fin 2) (ξ : Vec) (z : CVec),
    helicalSymbol σ ξ z =
      (1 / 2 : ℂ) •
        (transverseSymbol ξ z + (helicitySign σ : ℂ) • helicityOperator ξ z) :=
  @helicalSymbol_eq

example : ∀ (ξ : Vec) (z : CVec),
    transverseSymbol ξ (helicityOperator ξ z) = helicityOperator ξ z :=
  @transverseSymbol_helicityOperator

example : ∀ (ξ : Vec) (z : CVec),
    helicityOperator ξ (transverseSymbol ξ z) = helicityOperator ξ z :=
  @helicityOperator_transverseSymbol

example : ∀ {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec),
    helicityOperator ξ (helicityOperator ξ z) = transverseSymbol ξ z :=
  @helicityOperator_sq

example : ∀ (σ : Fin 2) {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec),
    helicalSymbol σ ξ (transverseSymbol ξ z) = helicalSymbol σ ξ z :=
  @helicalSymbol_transverseSymbol

example : ∀ (σ : Fin 2) {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec),
    helicityOperator ξ (helicalSymbol σ ξ z) =
      (helicitySign σ : ℂ) • helicalSymbol σ ξ z :=
  @helicityOperator_helicalSymbol

example : ∀ (σ : Fin 2) {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec),
    helicalSymbol σ ξ (helicityOperator ξ z) =
      (helicitySign σ : ℂ) • helicalSymbol σ ξ z :=
  @helicalSymbol_helicityOperator

example : ∀ (σ : Fin 2) {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec),
    Complex.I • complexCross ξ (helicalSymbol σ ξ z) =
      ((helicitySign σ : ℂ) * (‖ξ‖ : ℂ)) • helicalSymbol σ ξ z :=
  @complexCurl_helicalSymbol

example : ∀ (σ : Fin 2) {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec),
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I) •
        complexCross ξ (helicalSymbol σ ξ z) =
      ((helicitySign σ * (2 * Real.pi) * ‖ξ‖ : ℝ) : ℂ) •
        helicalSymbol σ ξ z :=
  @fourierCurl_helicalSymbol

example : ∀ (σ : Fin 2),
    (helicitySign σ : ℂ) * (helicitySign σ : ℂ) = 1 :=
  @helicitySign_mul_self

example : ∀ (σ : Fin 2) {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec),
    helicalSymbol σ ξ (helicalSymbol σ ξ z) = helicalSymbol σ ξ z :=
  @helicalSymbol_idempotent

example : ∀ (ξ : Vec) (z : CVec),
    helicalSymbol 0 ξ z + helicalSymbol 1 ξ z = transverseSymbol ξ z :=
  @helicalSymbol_sum

example : ∀ {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec),
    helicalSymbol 0 ξ (helicalSymbol 1 ξ z) = 0 :=
  @helicalSymbol_zero_one

example : ∀ {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec),
    helicalSymbol 1 ξ (helicalSymbol 0 ξ z) = 0 :=
  @helicalSymbol_one_zero

example : ∀ (ξ : Vec) (z w : CVec),
    inner ℂ (transverseSymbol ξ z) w = inner ℂ z (transverseSymbol ξ w) :=
  @transverseSymbol_selfAdjoint

example : ∀ (ξ : Vec) (z w : CVec),
    inner ℂ (complexCross ξ z) w = -inner ℂ z (complexCross ξ w) :=
  @complexCross_skewAdjoint

example : ∀ (ξ : Vec) (z w : CVec),
    inner ℂ (helicityOperator ξ z) w = inner ℂ z (helicityOperator ξ w) :=
  @helicityOperator_selfAdjoint

example : ∀ (σ : Fin 2) (ξ : Vec) (z w : CVec),
    inner ℂ (helicalSymbol σ ξ z) w = inner ℂ z (helicalSymbol σ ξ w) :=
  @helicalSymbol_selfAdjoint

example : ∀ {ξ : Vec} (hξ : ξ ≠ 0) (z w : CVec),
    inner ℂ (helicalSymbol 0 ξ z) (helicalSymbol 1 ξ w) = 0 :=
  @helicalSymbol_orthogonal

example : ∀ {ξ : Vec} (hξ : ξ ≠ 0) (z : CVec),
    ‖transverseSymbol ξ z‖ ^ 2 =
      ‖helicalSymbol 0 ξ z‖ ^ 2 + ‖helicalSymbol 1 ξ z‖ ^ 2 :=
  @helicalSymbol_norm_decomposition

example : ∀ {ξ : Vec} (hξ : ξ ≠ 0) {z : CVec} (hz : frequencyDot ξ z = 0),
    ‖z‖ ^ 2 = ‖helicalSymbol 0 ξ z‖ ^ 2 + ‖helicalSymbol 1 ξ z‖ ^ 2 :=
  @helicalSymbol_norm_decomposition_of_solenoidal

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.frequencyDot"
#check @MethbokeAddon.FDSNR3.frequencyDot
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.frequencyDot"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.frequencyDot"
#print axioms MethbokeAddon.FDSNR3.frequencyDot
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.frequencyDot"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.frequencyDot_add"
#check @MethbokeAddon.FDSNR3.frequencyDot_add
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.frequencyDot_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.frequencyDot_add"
#print axioms MethbokeAddon.FDSNR3.frequencyDot_add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.frequencyDot_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.frequencyDot_smul"
#check @MethbokeAddon.FDSNR3.frequencyDot_smul
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.frequencyDot_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.frequencyDot_smul"
#print axioms MethbokeAddon.FDSNR3.frequencyDot_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.frequencyDot_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.frequencyDot_sub"
#check @MethbokeAddon.FDSNR3.frequencyDot_sub
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.frequencyDot_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.frequencyDot_sub"
#print axioms MethbokeAddon.FDSNR3.frequencyDot_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.frequencyDot_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.frequencyDot_complexify"
#check @MethbokeAddon.FDSNR3.frequencyDot_complexify
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.frequencyDot_complexify"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.frequencyDot_complexify"
#print axioms MethbokeAddon.FDSNR3.frequencyDot_complexify
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.frequencyDot_complexify"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.frequencyDot_eq_inner"
#check @MethbokeAddon.FDSNR3.frequencyDot_eq_inner
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.frequencyDot_eq_inner"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.frequencyDot_eq_inner"
#print axioms MethbokeAddon.FDSNR3.frequencyDot_eq_inner
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.frequencyDot_eq_inner"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_eq"
#check @MethbokeAddon.FDSNR3.transverseSymbol_eq
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.transverseSymbol_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_eq"
#print axioms MethbokeAddon.FDSNR3.transverseSymbol_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.transverseSymbol_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_add"
#check @MethbokeAddon.FDSNR3.transverseSymbol_add
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.transverseSymbol_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_add"
#print axioms MethbokeAddon.FDSNR3.transverseSymbol_add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.transverseSymbol_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_smul"
#check @MethbokeAddon.FDSNR3.transverseSymbol_smul
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.transverseSymbol_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_smul"
#print axioms MethbokeAddon.FDSNR3.transverseSymbol_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.transverseSymbol_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.transverseLinearMap"
#check @MethbokeAddon.FDSNR3.transverseLinearMap
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.transverseLinearMap"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.transverseLinearMap"
#print axioms MethbokeAddon.FDSNR3.transverseLinearMap
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.transverseLinearMap"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexCross_add"
#check @MethbokeAddon.FDSNR3.complexCross_add
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexCross_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexCross_add"
#print axioms MethbokeAddon.FDSNR3.complexCross_add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexCross_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexCross_smul"
#check @MethbokeAddon.FDSNR3.complexCross_smul
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexCross_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexCross_smul"
#print axioms MethbokeAddon.FDSNR3.complexCross_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexCross_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexCrossLinearMap"
#check @MethbokeAddon.FDSNR3.complexCrossLinearMap
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexCrossLinearMap"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexCrossLinearMap"
#print axioms MethbokeAddon.FDSNR3.complexCrossLinearMap
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexCrossLinearMap"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexCross_sub"
#check @MethbokeAddon.FDSNR3.complexCross_sub
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexCross_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexCross_sub"
#print axioms MethbokeAddon.FDSNR3.complexCross_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexCross_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_add"
#check @MethbokeAddon.FDSNR3.helicalSymbol_add
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_add"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol_add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_smul"
#check @MethbokeAddon.FDSNR3.helicalSymbol_smul
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_smul"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalLinearMap"
#check @MethbokeAddon.FDSNR3.helicalLinearMap
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalLinearMap"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalLinearMap"
#print axioms MethbokeAddon.FDSNR3.helicalLinearMap
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalLinearMap"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_packetRotate"
#check @MethbokeAddon.FDSNR3.helicalSymbol_packetRotate
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol_packetRotate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_packetRotate"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol_packetRotate
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol_packetRotate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.norm_helicalSymbol_packetRotate"
#check @MethbokeAddon.FDSNR3.norm_helicalSymbol_packetRotate
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.norm_helicalSymbol_packetRotate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.norm_helicalSymbol_packetRotate"
#print axioms MethbokeAddon.FDSNR3.norm_helicalSymbol_packetRotate
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.norm_helicalSymbol_packetRotate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalPower_eq_of_fourier_phase"
#check @MethbokeAddon.FDSNR3.helicalPower_eq_of_fourier_phase
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalPower_eq_of_fourier_phase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalPower_eq_of_fourier_phase"
#print axioms MethbokeAddon.FDSNR3.helicalPower_eq_of_fourier_phase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalPower_eq_of_fourier_phase"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.frequencyDot_transverseSymbol"
#check @MethbokeAddon.FDSNR3.frequencyDot_transverseSymbol
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.frequencyDot_transverseSymbol"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.frequencyDot_transverseSymbol"
#print axioms MethbokeAddon.FDSNR3.frequencyDot_transverseSymbol
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.frequencyDot_transverseSymbol"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_of_frequencyDot_eq_zero"
#check @MethbokeAddon.FDSNR3.transverseSymbol_of_frequencyDot_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.transverseSymbol_of_frequencyDot_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_of_frequencyDot_eq_zero"
#print axioms MethbokeAddon.FDSNR3.transverseSymbol_of_frequencyDot_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.transverseSymbol_of_frequencyDot_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_idempotent"
#check @MethbokeAddon.FDSNR3.transverseSymbol_idempotent
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.transverseSymbol_idempotent"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_idempotent"
#print axioms MethbokeAddon.FDSNR3.transverseSymbol_idempotent
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.transverseSymbol_idempotent"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexCross_complexify"
#check @MethbokeAddon.FDSNR3.complexCross_complexify
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexCross_complexify"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexCross_complexify"
#print axioms MethbokeAddon.FDSNR3.complexCross_complexify
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexCross_complexify"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.frequencyDot_complexCross"
#check @MethbokeAddon.FDSNR3.frequencyDot_complexCross
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.frequencyDot_complexCross"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.frequencyDot_complexCross"
#print axioms MethbokeAddon.FDSNR3.frequencyDot_complexCross
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.frequencyDot_complexCross"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_complexCross"
#check @MethbokeAddon.FDSNR3.transverseSymbol_complexCross
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.transverseSymbol_complexCross"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_complexCross"
#print axioms MethbokeAddon.FDSNR3.transverseSymbol_complexCross
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.transverseSymbol_complexCross"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexCross_transverseSymbol"
#check @MethbokeAddon.FDSNR3.complexCross_transverseSymbol
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexCross_transverseSymbol"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexCross_transverseSymbol"
#print axioms MethbokeAddon.FDSNR3.complexCross_transverseSymbol
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexCross_transverseSymbol"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexCross_twice"
#check @MethbokeAddon.FDSNR3.complexCross_twice
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexCross_twice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexCross_twice"
#print axioms MethbokeAddon.FDSNR3.complexCross_twice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexCross_twice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicityOperator"
#check @MethbokeAddon.FDSNR3.helicityOperator
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicityOperator"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicityOperator"
#print axioms MethbokeAddon.FDSNR3.helicityOperator
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicityOperator"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicityOperator_add"
#check @MethbokeAddon.FDSNR3.helicityOperator_add
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicityOperator_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicityOperator_add"
#print axioms MethbokeAddon.FDSNR3.helicityOperator_add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicityOperator_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicityOperator_smul"
#check @MethbokeAddon.FDSNR3.helicityOperator_smul
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicityOperator_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicityOperator_smul"
#print axioms MethbokeAddon.FDSNR3.helicityOperator_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicityOperator_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_eq"
#check @MethbokeAddon.FDSNR3.helicalSymbol_eq
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_eq"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_helicityOperator"
#check @MethbokeAddon.FDSNR3.transverseSymbol_helicityOperator
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.transverseSymbol_helicityOperator"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_helicityOperator"
#print axioms MethbokeAddon.FDSNR3.transverseSymbol_helicityOperator
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.transverseSymbol_helicityOperator"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicityOperator_transverseSymbol"
#check @MethbokeAddon.FDSNR3.helicityOperator_transverseSymbol
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicityOperator_transverseSymbol"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicityOperator_transverseSymbol"
#print axioms MethbokeAddon.FDSNR3.helicityOperator_transverseSymbol
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicityOperator_transverseSymbol"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicityOperator_sq"
#check @MethbokeAddon.FDSNR3.helicityOperator_sq
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicityOperator_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicityOperator_sq"
#print axioms MethbokeAddon.FDSNR3.helicityOperator_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicityOperator_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_transverseSymbol"
#check @MethbokeAddon.FDSNR3.helicalSymbol_transverseSymbol
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol_transverseSymbol"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_transverseSymbol"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol_transverseSymbol
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol_transverseSymbol"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicityOperator_helicalSymbol"
#check @MethbokeAddon.FDSNR3.helicityOperator_helicalSymbol
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicityOperator_helicalSymbol"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicityOperator_helicalSymbol"
#print axioms MethbokeAddon.FDSNR3.helicityOperator_helicalSymbol
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicityOperator_helicalSymbol"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_helicityOperator"
#check @MethbokeAddon.FDSNR3.helicalSymbol_helicityOperator
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol_helicityOperator"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_helicityOperator"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol_helicityOperator
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol_helicityOperator"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexCurl_helicalSymbol"
#check @MethbokeAddon.FDSNR3.complexCurl_helicalSymbol
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexCurl_helicalSymbol"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexCurl_helicalSymbol"
#print axioms MethbokeAddon.FDSNR3.complexCurl_helicalSymbol
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexCurl_helicalSymbol"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierCurl_helicalSymbol"
#check @MethbokeAddon.FDSNR3.fourierCurl_helicalSymbol
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierCurl_helicalSymbol"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierCurl_helicalSymbol"
#print axioms MethbokeAddon.FDSNR3.fourierCurl_helicalSymbol
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierCurl_helicalSymbol"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicitySign_mul_self"
#check @MethbokeAddon.FDSNR3.helicitySign_mul_self
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicitySign_mul_self"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicitySign_mul_self"
#print axioms MethbokeAddon.FDSNR3.helicitySign_mul_self
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicitySign_mul_self"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_idempotent"
#check @MethbokeAddon.FDSNR3.helicalSymbol_idempotent
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol_idempotent"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_idempotent"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol_idempotent
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol_idempotent"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_sum"
#check @MethbokeAddon.FDSNR3.helicalSymbol_sum
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol_sum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_sum"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol_sum
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol_sum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_zero_one"
#check @MethbokeAddon.FDSNR3.helicalSymbol_zero_one
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol_zero_one"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_zero_one"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol_zero_one
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol_zero_one"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_one_zero"
#check @MethbokeAddon.FDSNR3.helicalSymbol_one_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol_one_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_one_zero"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol_one_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol_one_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_selfAdjoint"
#check @MethbokeAddon.FDSNR3.transverseSymbol_selfAdjoint
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.transverseSymbol_selfAdjoint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol_selfAdjoint"
#print axioms MethbokeAddon.FDSNR3.transverseSymbol_selfAdjoint
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.transverseSymbol_selfAdjoint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexCross_skewAdjoint"
#check @MethbokeAddon.FDSNR3.complexCross_skewAdjoint
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexCross_skewAdjoint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexCross_skewAdjoint"
#print axioms MethbokeAddon.FDSNR3.complexCross_skewAdjoint
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexCross_skewAdjoint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicityOperator_selfAdjoint"
#check @MethbokeAddon.FDSNR3.helicityOperator_selfAdjoint
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicityOperator_selfAdjoint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicityOperator_selfAdjoint"
#print axioms MethbokeAddon.FDSNR3.helicityOperator_selfAdjoint
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicityOperator_selfAdjoint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_selfAdjoint"
#check @MethbokeAddon.FDSNR3.helicalSymbol_selfAdjoint
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol_selfAdjoint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_selfAdjoint"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol_selfAdjoint
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol_selfAdjoint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_orthogonal"
#check @MethbokeAddon.FDSNR3.helicalSymbol_orthogonal
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol_orthogonal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_orthogonal"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol_orthogonal
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol_orthogonal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_norm_decomposition"
#check @MethbokeAddon.FDSNR3.helicalSymbol_norm_decomposition
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol_norm_decomposition"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_norm_decomposition"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol_norm_decomposition
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol_norm_decomposition"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_norm_decomposition_of_solenoidal"
#check @MethbokeAddon.FDSNR3.helicalSymbol_norm_decomposition_of_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol_norm_decomposition_of_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol_norm_decomposition_of_solenoidal"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol_norm_decomposition_of_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol_norm_decomposition_of_solenoidal"

