import MethbokeAddon.FDSN.CharacterTriad
import MethbokeAddon.WeakFouriermanB.PhysicalFourier

/-!
# Actual smooth periodic Fourier translation covariance

The proof uses the already constructed rapid Fourier synthesis and actual
coefficient-recovery theorem. No translation-covariance premise is assumed.
All frequencies, including zero, are retained.
-/

noncomputable section

open SingularClosure
open scoped BigOperators ContDiff ComplexConjugate

namespace MethbokeAddon.FDSN

theorem fourierCharacter_add_argument (k : Frequency) (x a : Vec) :
    fourierCharacter k (x + a) = fourierCharacter k x * fourierCharacter k a := by
  simp only [fourierCharacter_eq_exp_phase, map_add, Complex.exp_add]

/-- The exact coefficient array of a positive spatial translation. -/
def translatedCoefficients (a : Vec) (c : FourierCoeff) : FourierCoeff :=
  fun k i => fourierCharacter k a * c k i

theorem translatedCoefficients_reality (a : Vec) (c : FourierCoeff)
    (hc : SpectralReality c) : SpectralReality (translatedCoefficients a c) := by
  intro k i
  change fourierCharacter (-k) a * c (-k) i = star (fourierCharacter k a * c k i)
  rw [fourierCharacter_neg, hc k i, star_mul]
  ring

theorem translatedCoefficients_rapid (a : Vec) (c : FourierCoeff)
    (hc : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i)) :
    ∀ i : Fin 3, RapidScalarFourier (fun k => translatedCoefficients a c k i) := by
  intro i m
  simpa only [translatedCoefficients, norm_mul, fourierCharacter_norm, one_mul]
    using hc i m

theorem smoothFourierSynthesis_translation (a : Vec) (c : FourierCoeff) :
    smoothFourierSynthesis (translatedCoefficients a c) =
      fun x => smoothFourierSynthesis c (x + a) := by
  funext x
  ext i
  change (∑' k : Frequency, fourierCharacter k x *
      (fourierCharacter k a * c k i)).re =
    (∑' k : Frequency, fourierCharacter k (x + a) * c k i).re
  congr 1
  apply tsum_congr
  intro k
  rw [fourierCharacter_add_argument]
  ring

/-- Actual Fourier coefficients of a translated smooth periodic vector field. -/
theorem datumFourierCoeff_translation (v : Field) (hv : ContDiff ℝ ∞ v)
    (hp : SpatialPeriodic v) (a : Vec) :
    datumFourierCoeff (fun x => v (x + a)) =
      translatedCoefficients a (datumFourierCoeff v) := by
  have hr : ∀ i : Fin 3, RapidScalarFourier (fun k => datumFourierCoeff v k i) :=
    ALL_SOBOLEV_IMP_RAPID_SCALAR (datumFourierCoeff v)
      (fun s => SMOOTH_DATUM_MEM_TORUS_SOBOLEV s v hv hp)
  calc
    datumFourierCoeff (fun x => v (x + a)) =
        datumFourierCoeff (smoothFourierSynthesis
          (translatedCoefficients a (datumFourierCoeff v))) := by
      rw [smoothFourierSynthesis_translation,
        MethbokeAddon.WeakFouriermanB.smoothFourierSynthesis_datum_eq v hv hp]
    _ = translatedCoefficients a (datumFourierCoeff v) :=
      datumFourierCoeff_smoothFourierSynthesis _
        (translatedCoefficients_rapid a _ hr)
        (translatedCoefficients_reality a _ (datumFourierCoeff_reality v))

/-- Any complex-linear modal observation has the same translation character.
Helical coefficient extraction can be supplied by the concrete helical API. -/
def modalObservation (L : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) (v : Field) (k : Frequency) : ℂ :=
  L (datumFourierCoeff v k)

theorem modalObservation_translation (L : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (a : Vec) (k : Frequency) :
    modalObservation L (fun x => v (x + a)) k =
      fourierCharacter k a * modalObservation L v k := by
  unfold modalObservation
  rw [datumFourierCoeff_translation v hv hp a]
  change L (fourierCharacter k a • datumFourierCoeff v k) =
    fourierCharacter k a * L (datumFourierCoeff v k)
  rw [map_smul, smul_eq_mul]

/-- Correlation of three actual Fourier observations of a physical field. -/
def fieldTriadCorrelation (k1 k2 k3 : Frequency)
    (L1 L2 L3 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) (v : Field) : ℂ :=
  triadCorrelation (modalObservation L1 v k1)
    (modalObservation L2 v k2) (modalObservation L3 v k3)

theorem fieldTriadCorrelation_translation
    (k1 k2 k3 : Frequency) (htriad : k1 + k2 = k3)
    (L1 L2 L3 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (a : Vec) :
    fieldTriadCorrelation k1 k2 k3 L1 L2 L3 (fun x => v (x + a)) =
      fieldTriadCorrelation k1 k2 k3 L1 L2 L3 v := by
  unfold fieldTriadCorrelation
  rw [modalObservation_translation L1 v hv hp a k1,
    modalObservation_translation L2 v hv hp a k2,
    modalObservation_translation L3 v hv hp a k3]
  exact triadCorrelation_native_character k1 k2 k3 htriad a _ _ _

/-- Unequal actual Fourier triad correlations exclude every spatial translation. -/
theorem fields_not_translation_of_triadCorrelation_ne
    (k1 k2 k3 : Frequency) (htriad : k1 + k2 = k3)
    (L1 L2 L3 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)
    (u v : Field) (hu : ContDiff ℝ ∞ u) (hp : SpatialPeriodic u)
    (hne : fieldTriadCorrelation k1 k2 k3 L1 L2 L3 u ≠
      fieldTriadCorrelation k1 k2 k3 L1 L2 L3 v) :
    ¬ ∃ a : Vec, ∀ x : Vec, u (x + a) = v x := by
  rintro ⟨a, ha⟩
  have hfun : (fun x => u (x + a)) = v := funext ha
  apply hne
  calc
    fieldTriadCorrelation k1 k2 k3 L1 L2 L3 u =
        fieldTriadCorrelation k1 k2 k3 L1 L2 L3 (fun x => u (x + a)) :=
      (fieldTriadCorrelation_translation k1 k2 k3 htriad L1 L2 L3 u hu hp a).symm
    _ = fieldTriadCorrelation k1 k2 k3 L1 L2 L3 v := by rw [hfun]

end MethbokeAddon.FDSN
