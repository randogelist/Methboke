import FDSNFourierTranslation.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/- Explicit full-type consumers. Root supplies imports and audit sentinels. -/

noncomputable section
open SingularClosure
open MethbokeAddon.FDSN
open scoped BigOperators ContDiff ComplexConjugate

example : (translatedCoefficients : Vec → FourierCoeff → FourierCoeff) =
    (fun a c k i => fourierCharacter k a * c k i) := rfl

example : (modalObservation : ((Fin 3 → ℂ) →ₗ[ℂ] ℂ) → Field → Frequency → ℂ) =
    (fun L v k => L (datumFourierCoeff v k)) := rfl

example : (fieldTriadCorrelation : Frequency → Frequency → Frequency →
    ((Fin 3 → ℂ) →ₗ[ℂ] ℂ) → ((Fin 3 → ℂ) →ₗ[ℂ] ℂ) →
    ((Fin 3 → ℂ) →ₗ[ℂ] ℂ) → Field → ℂ) =
    (fun k1 k2 k3 L1 L2 L3 v => triadCorrelation
      (modalObservation L1 v k1) (modalObservation L2 v k2)
      (modalObservation L3 v k3)) := rfl

example : ∀ (k : Frequency) (x a : Vec),
    fourierCharacter k (x + a) = fourierCharacter k x * fourierCharacter k a :=
  @MethbokeAddon.FDSN.fourierCharacter_add_argument

example : ∀ (a : Vec) (c : FourierCoeff)
    (hc : SpectralReality c),
    SpectralReality (translatedCoefficients a c) :=
  @MethbokeAddon.FDSN.translatedCoefficients_reality

example : ∀ (a : Vec) (c : FourierCoeff)
    (hc : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i)),
    ∀ i : Fin 3, RapidScalarFourier (fun k => translatedCoefficients a c k i) :=
  @MethbokeAddon.FDSN.translatedCoefficients_rapid

example : ∀ (a : Vec) (c : FourierCoeff),
    smoothFourierSynthesis (translatedCoefficients a c) =
      fun x => smoothFourierSynthesis c (x + a) :=
  @MethbokeAddon.FDSN.smoothFourierSynthesis_translation

example : ∀ (v : Field) (hv : ContDiff ℝ ∞ v)
    (hp : SpatialPeriodic v) (a : Vec),
    datumFourierCoeff (fun x => v (x + a)) =
      translatedCoefficients a (datumFourierCoeff v) :=
  @MethbokeAddon.FDSN.datumFourierCoeff_translation

example : ∀ (L : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (a : Vec) (k : Frequency),
    modalObservation L (fun x => v (x + a)) k =
      fourierCharacter k a * modalObservation L v k :=
  @MethbokeAddon.FDSN.modalObservation_translation

example : ∀ (k1 k2 k3 : Frequency) (htriad : k1 + k2 = k3)
    (L1 L2 L3 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (a : Vec),
    fieldTriadCorrelation k1 k2 k3 L1 L2 L3 (fun x => v (x + a)) =
      fieldTriadCorrelation k1 k2 k3 L1 L2 L3 v :=
  @MethbokeAddon.FDSN.fieldTriadCorrelation_translation

example : ∀ (k1 k2 k3 : Frequency) (htriad : k1 + k2 = k3)
    (L1 L2 L3 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)
    (u v : Field) (hu : ContDiff ℝ ∞ u) (hp : SpatialPeriodic u)
    (hne : fieldTriadCorrelation k1 k2 k3 L1 L2 L3 u ≠
      fieldTriadCorrelation k1 k2 k3 L1 L2 L3 v),
    ¬ ∃ a : Vec, ∀ x : Vec, u (x + a) = v x :=
  @MethbokeAddon.FDSN.fields_not_translation_of_triadCorrelation_ne

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.fourierCharacter_add_argument"
#check @MethbokeAddon.FDSN.fourierCharacter_add_argument
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.fourierCharacter_add_argument"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.fourierCharacter_add_argument"
#print axioms MethbokeAddon.FDSN.fourierCharacter_add_argument
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.fourierCharacter_add_argument"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.translatedCoefficients"
#check @MethbokeAddon.FDSN.translatedCoefficients
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.translatedCoefficients"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.translatedCoefficients"
#print axioms MethbokeAddon.FDSN.translatedCoefficients
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.translatedCoefficients"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.translatedCoefficients_reality"
#check @MethbokeAddon.FDSN.translatedCoefficients_reality
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.translatedCoefficients_reality"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.translatedCoefficients_reality"
#print axioms MethbokeAddon.FDSN.translatedCoefficients_reality
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.translatedCoefficients_reality"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.translatedCoefficients_rapid"
#check @MethbokeAddon.FDSN.translatedCoefficients_rapid
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.translatedCoefficients_rapid"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.translatedCoefficients_rapid"
#print axioms MethbokeAddon.FDSN.translatedCoefficients_rapid
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.translatedCoefficients_rapid"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.smoothFourierSynthesis_translation"
#check @MethbokeAddon.FDSN.smoothFourierSynthesis_translation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.smoothFourierSynthesis_translation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.smoothFourierSynthesis_translation"
#print axioms MethbokeAddon.FDSN.smoothFourierSynthesis_translation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.smoothFourierSynthesis_translation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.datumFourierCoeff_translation"
#check @MethbokeAddon.FDSN.datumFourierCoeff_translation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.datumFourierCoeff_translation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.datumFourierCoeff_translation"
#print axioms MethbokeAddon.FDSN.datumFourierCoeff_translation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.datumFourierCoeff_translation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.modalObservation"
#check @MethbokeAddon.FDSN.modalObservation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.modalObservation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.modalObservation"
#print axioms MethbokeAddon.FDSN.modalObservation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.modalObservation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.modalObservation_translation"
#check @MethbokeAddon.FDSN.modalObservation_translation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.modalObservation_translation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.modalObservation_translation"
#print axioms MethbokeAddon.FDSN.modalObservation_translation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.modalObservation_translation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.fieldTriadCorrelation"
#check @MethbokeAddon.FDSN.fieldTriadCorrelation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.fieldTriadCorrelation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.fieldTriadCorrelation"
#print axioms MethbokeAddon.FDSN.fieldTriadCorrelation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.fieldTriadCorrelation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.fieldTriadCorrelation_translation"
#check @MethbokeAddon.FDSN.fieldTriadCorrelation_translation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.fieldTriadCorrelation_translation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.fieldTriadCorrelation_translation"
#print axioms MethbokeAddon.FDSN.fieldTriadCorrelation_translation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.fieldTriadCorrelation_translation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.fields_not_translation_of_triadCorrelation_ne"
#check @MethbokeAddon.FDSN.fields_not_translation_of_triadCorrelation_ne
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.fields_not_translation_of_triadCorrelation_ne"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.fields_not_translation_of_triadCorrelation_ne"
#print axioms MethbokeAddon.FDSN.fields_not_translation_of_triadCorrelation_ne
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.fields_not_translation_of_triadCorrelation_ne"

