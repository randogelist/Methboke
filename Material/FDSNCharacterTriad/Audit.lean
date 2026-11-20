import FDSNCharacterTriad.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/- Explicit full-type consumers. Root supplies imports and audit sentinels. -/

noncomputable section
open SingularClosure
open MethbokeAddon.FDSN
open scoped BigOperators ContDiff ComplexConjugate

example : (characterAngle : Frequency → Vec → ℝ) =
    (fun k x => 2 * Real.pi * ∑ i : Fin 3, (k i : ℝ) * x i) := rfl

example : ∀ (k : Frequency) (x : Vec),
    fourierCharacter k x = phase (characterAngle k x) :=
  @MethbokeAddon.FDSN.fourierCharacter_eq_phase

example : ∀ (k l : Frequency) (x : Vec),
    characterAngle (k + l) x = characterAngle k x + characterAngle l x :=
  @MethbokeAddon.FDSN.characterAngle_add

example : ∀ (k l : Frequency) (x : Vec),
    fourierCharacter (k + l) x = fourierCharacter k x * fourierCharacter l x :=
  @MethbokeAddon.FDSN.fourierCharacter_add_frequency

example : ∀ (k1 k2 k3 : Frequency)
    (htriad : k1 + k2 = k3) (x : Vec) (a b c : ℂ),
    triadCorrelation (fourierCharacter k1 x * a)
      (fourierCharacter k2 x * b) (fourierCharacter k3 x * c) =
      triadCorrelation a b c :=
  @MethbokeAddon.FDSN.triadCorrelation_native_character

example : ∀ (k1 k2 k3 : Frequency) (htriad : k1 + k2 = k3)
    {a b c : ℂ} (hB : triadCorrelation a b c ≠ 0)
    {lambda eta : ℝ} (hlambda : |lambda| < Real.pi / 4)
    (heta : |eta| < Real.pi / 4) (hne : lambda ≠ eta) (x : Vec),
    ¬ (fourierCharacter k1 x * a = a ∧
      fourierCharacter k2 x * b = b ∧
      fourierCharacter k3 x * (phase lambda * c) = phase eta * c) :=
  @MethbokeAddon.FDSN.triad_phase_not_character_translation

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.characterAngle"
#check @MethbokeAddon.FDSN.characterAngle
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.characterAngle"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.characterAngle"
#print axioms MethbokeAddon.FDSN.characterAngle
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.characterAngle"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.fourierCharacter_eq_phase"
#check @MethbokeAddon.FDSN.fourierCharacter_eq_phase
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.fourierCharacter_eq_phase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.fourierCharacter_eq_phase"
#print axioms MethbokeAddon.FDSN.fourierCharacter_eq_phase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.fourierCharacter_eq_phase"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.characterAngle_add"
#check @MethbokeAddon.FDSN.characterAngle_add
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.characterAngle_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.characterAngle_add"
#print axioms MethbokeAddon.FDSN.characterAngle_add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.characterAngle_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.fourierCharacter_add_frequency"
#check @MethbokeAddon.FDSN.fourierCharacter_add_frequency
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.fourierCharacter_add_frequency"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.fourierCharacter_add_frequency"
#print axioms MethbokeAddon.FDSN.fourierCharacter_add_frequency
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.fourierCharacter_add_frequency"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.triadCorrelation_native_character"
#check @MethbokeAddon.FDSN.triadCorrelation_native_character
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.triadCorrelation_native_character"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.triadCorrelation_native_character"
#print axioms MethbokeAddon.FDSN.triadCorrelation_native_character
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.triadCorrelation_native_character"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.triad_phase_not_character_translation"
#check @MethbokeAddon.FDSN.triad_phase_not_character_translation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.triad_phase_not_character_translation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.triad_phase_not_character_translation"
#print axioms MethbokeAddon.FDSN.triad_phase_not_character_translation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.triad_phase_not_character_translation"

