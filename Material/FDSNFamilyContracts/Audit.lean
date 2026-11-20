import FDSNFamilyContracts.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

open Set SingularClosure MethbokeAddon.FDSN
open scoped BigOperators ContDiff

noncomputable section

example : HelicalFrameArray = (Frequency → Fin 2 → Fin 3 → ℂ) := rfl

example (σ : Fin 2) :
    helicitySign σ =
      (if σ = 0 then 1 else -1) := rfl

example (k : Frequency) :
    frequencyLength k =
      (Real.sqrt (∑ i : Fin 3, (k i : ℝ) ^ 2)) := rfl

example (k : Frequency) (v : Fin 3 → ℂ) :
    helicalCurl k v =
      (fun i => (2 * (Real.pi : ℂ) * Complex.I) *
    crossProduct (fun j : Fin 3 => (k j : ℂ)) v i) := rfl

example (h : HelicalFrameArray) :
    IsHelicalFrame h ↔
      ((∀ k : Frequency, k ≠ 0 → ∀ σ τ : Fin 2,
    (∑ i : Fin 3, star (h k σ i) * h k τ i) = if σ = τ then 1 else 0) ∧
  (∀ k : Frequency, k ≠ 0 → ∀ σ : Fin 2, ∀ i : Fin 3,
    helicalCurl k (h k σ) i =
      ((helicitySign σ * (2 * Real.pi) * frequencyLength k : ℝ) : ℂ) * h k σ i) ∧
  (∀ k : Frequency, k ≠ 0 → ∀ σ : Fin 2, ∀ i : Fin 3,
    h (-k) σ i = star (h k σ i))) := Iff.rfl

example (h : HelicalFrameArray) (v : Field)
    (k : Frequency) (σ : Fin 2) :
    helicalCoefficient h v k σ =
      (helicalObservation (h k σ) (datumFourierCoeff v k)) := rfl

example (a b : ℝ) (V : Velocity) :
    CompactTemporalCorrection a b V ↔
      (ContDiff ℝ ∞ (fun z : ℝ × Vec => V z.1 z.2) ∧
  (∀ t : ℝ, SpatialPeriodic (V t)) ∧
  HasCompactSupport V ∧ tsupport V ⊆ Ioo a b) := Iff.rfl

example (r : ℕ) (a b : ℝ) (V : Velocity) :
    spacetimeCrNorm r a b V =
      (∑ n ∈ Finset.range (r + 1),
    sSup ((fun z : ℝ × Vec =>
      ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => V y.1 y.2) z‖) ''
        (Icc a b ×ˢ unitCube))) := rfl

example (ν T a b ε : ℝ)
    (u : Velocity) (p : Pressure) (F : Velocity)
    (U G : ℝ → Velocity) :
    ExactRealizationAndAgreement ν T a b ε u p F U G ↔
      (∀ lambda : ℝ, |lambda| < ε →
    PreterminalNSE ν T (U lambda) p (G lambda) ∧
    MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce (G lambda) ∧
    U lambda 0 = u 0 ∧
    CompactTemporalCorrection a b (U lambda - u) ∧
    CompactTemporalCorrection a b (G lambda - F) ∧
    CofinalVelocityBlowup T (U lambda)) := Iff.rfl

example (h : HelicalFrameArray)
    (T ε : ℝ) (u : Velocity) (U : ℝ → Velocity) :
    CompleteHelicalPowerPreservation h T ε u U ↔
      (∀ lambda : ℝ, |lambda| < ε → ∀ t ∈ Ico (0 : ℝ) T,
    (∀ k : Frequency, k ≠ 0 → ∀ σ : Fin 2,
      Complex.normSq (helicalCoefficient h (U lambda t) k σ) =
        Complex.normSq (helicalCoefficient h (u t) k σ)) ∧
    datumFourierCoeff (U lambda t) 0 = datumFourierCoeff (u t) 0) := Iff.rfl

example (tstar ε : ℝ) (U : ℝ → Velocity) :
    TranslationSeparation tstar ε U ↔
      (∀ lambda η : ℝ, |lambda| < ε → |η| < ε → lambda ≠ η →
    ¬ ∃ y : Vec, ∀ x : Vec, U lambda tstar x = U η tstar (x + y)) := Iff.rfl

example (T ε : ℝ) (G : ℝ → Velocity) :
    ProjectedForceSeparation T ε G ↔
      (∀ lambda η : ℝ, |lambda| < ε → |η| < ε → lambda ≠ η →
    ∃ t ∈ Ico (0 : ℝ) T, ∃ k : Frequency, ∃ i : Fin 3,
      coefficientLeray k (datumFourierCoeff (G lambda t) k) i ≠
        coefficientLeray k (datumFourierCoeff (G η t) k) i) := Iff.rfl

example (a b ε : ℝ) (u F : Velocity)
    (U G : ℝ → Velocity) :
    SmoothSmallness a b ε u F U G ↔
      (∀ r : ℕ, ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
    ∀ lambda : ℝ, |lambda| < min ε δ →
      spacetimeCrNorm r a b (U lambda - u) +
        spacetimeCrNorm r a b (G lambda - F) ≤ C * |lambda|) := Iff.rfl

example (h : HelicalFrameArray) (ν T : ℝ)
    (u : Velocity) (p : Pressure) (F : Velocity) :
    FamilyFor h ν T u p F ↔
      (∀ s ∈ Ico (0 : ℝ) T,
    ∃ a b tstar ε : ℝ, ∃ U G : ℝ → Velocity,
      s < a ∧ a < b ∧ b < T ∧ tstar ∈ Ioo a b ∧ 0 < ε ∧
      U 0 = u ∧ G 0 = F ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
        (U q.1 - u) q.2.1 q.2.2) {q | |q.1| < ε} ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
        (G q.1 - F) q.2.1 q.2.2) {q | |q.1| < ε} ∧
      ExactRealizationAndAgreement ν T a b ε u p F U G ∧
      CompleteHelicalPowerPreservation h T ε u U ∧
      TranslationSeparation tstar ε U ∧
      ProjectedForceSeparation T ε G ∧
      SmoothSmallness a b ε u F U G) := Iff.rfl

example (ν T : ℝ) (u : Velocity) (p : Pressure) (F : Velocity) :
    Family ν T u p F ↔
      (∀ h : HelicalFrameArray, IsHelicalFrame h → FamilyFor h ν T u p F) := Iff.rfl

example (h v : Fin 3 → ℂ) :
    helicalObservation h v = ∑ i : Fin 3, star (h i) * v i := rfl

example {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (H : ∀ h : HelicalFrameArray, FamilyFor h ν T u p F) :
    Family ν T u p F := family_of_all_frame_arrays H

example {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (H : Family ν T u p F) {h : HelicalFrameArray} (hh : IsHelicalFrame h) :
    FamilyFor h ν T u p F := Family.for_fixed_helical_frame H hh



















end

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.helicitySign"
#check @MethbokeAddon.FDSN.helicitySign
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.helicitySign"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.helicitySign"
#print axioms MethbokeAddon.FDSN.helicitySign
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.helicitySign"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.frequencyLength"
#check @MethbokeAddon.FDSN.frequencyLength
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.frequencyLength"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.frequencyLength"
#print axioms MethbokeAddon.FDSN.frequencyLength
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.frequencyLength"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.helicalCurl"
#check @MethbokeAddon.FDSN.helicalCurl
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.helicalCurl"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.helicalCurl"
#print axioms MethbokeAddon.FDSN.helicalCurl
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.helicalCurl"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.IsHelicalFrame"
#check @MethbokeAddon.FDSN.IsHelicalFrame
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.IsHelicalFrame"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.IsHelicalFrame"
#print axioms MethbokeAddon.FDSN.IsHelicalFrame
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.IsHelicalFrame"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.helicalObservation"
#check @MethbokeAddon.FDSN.helicalObservation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.helicalObservation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.helicalObservation"
#print axioms MethbokeAddon.FDSN.helicalObservation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.helicalObservation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.helicalCoefficient"
#check @MethbokeAddon.FDSN.helicalCoefficient
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.helicalCoefficient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.helicalCoefficient"
#print axioms MethbokeAddon.FDSN.helicalCoefficient
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.helicalCoefficient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.CompactTemporalCorrection"
#check @MethbokeAddon.FDSN.CompactTemporalCorrection
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.CompactTemporalCorrection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.CompactTemporalCorrection"
#print axioms MethbokeAddon.FDSN.CompactTemporalCorrection
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.CompactTemporalCorrection"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.spacetimeCrNorm"
#check @MethbokeAddon.FDSN.spacetimeCrNorm
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.spacetimeCrNorm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.spacetimeCrNorm"
#print axioms MethbokeAddon.FDSN.spacetimeCrNorm
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.spacetimeCrNorm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.ExactRealizationAndAgreement"
#check @MethbokeAddon.FDSN.ExactRealizationAndAgreement
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.ExactRealizationAndAgreement"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.ExactRealizationAndAgreement"
#print axioms MethbokeAddon.FDSN.ExactRealizationAndAgreement
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.ExactRealizationAndAgreement"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.CompleteHelicalPowerPreservation"
#check @MethbokeAddon.FDSN.CompleteHelicalPowerPreservation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.CompleteHelicalPowerPreservation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.CompleteHelicalPowerPreservation"
#print axioms MethbokeAddon.FDSN.CompleteHelicalPowerPreservation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.CompleteHelicalPowerPreservation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.TranslationSeparation"
#check @MethbokeAddon.FDSN.TranslationSeparation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.TranslationSeparation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.TranslationSeparation"
#print axioms MethbokeAddon.FDSN.TranslationSeparation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.TranslationSeparation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.ProjectedForceSeparation"
#check @MethbokeAddon.FDSN.ProjectedForceSeparation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.ProjectedForceSeparation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.ProjectedForceSeparation"
#print axioms MethbokeAddon.FDSN.ProjectedForceSeparation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.ProjectedForceSeparation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.SmoothSmallness"
#check @MethbokeAddon.FDSN.SmoothSmallness
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.SmoothSmallness"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.SmoothSmallness"
#print axioms MethbokeAddon.FDSN.SmoothSmallness
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.SmoothSmallness"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.FamilyFor"
#check @MethbokeAddon.FDSN.FamilyFor
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.FamilyFor"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.FamilyFor"
#print axioms MethbokeAddon.FDSN.FamilyFor
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.FamilyFor"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.Family"
#check @MethbokeAddon.FDSN.Family
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.Family"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.Family"
#print axioms MethbokeAddon.FDSN.Family
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.Family"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.family_of_all_frame_arrays"
#check @MethbokeAddon.FDSN.family_of_all_frame_arrays
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.family_of_all_frame_arrays"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.family_of_all_frame_arrays"
#print axioms MethbokeAddon.FDSN.family_of_all_frame_arrays
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.family_of_all_frame_arrays"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.Family.for_fixed_helical_frame"
#check @MethbokeAddon.FDSN.Family.for_fixed_helical_frame
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.Family.for_fixed_helical_frame"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.Family.for_fixed_helical_frame"
#print axioms MethbokeAddon.FDSN.Family.for_fixed_helical_frame
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.Family.for_fixed_helical_frame"

