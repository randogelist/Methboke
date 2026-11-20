import FDSNLocalizedPairSeparation.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/- Explicit full-type consumers; root supplies imports and audit sentinels. -/

noncomputable section
open Set SingularClosure MethbokeAddon.FDSN
open scoped BigOperators ContDiff Topology

example (i : Fin 3) : coordinateObservation i =
    ({ toFun := fun v : Fin 3 → ℂ => v i
       map_add' := by intros; rfl
       map_smul' := by intros; rfl } : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) := rfl

example : ∀ {v : Fin 3 → ℂ} (hv : v ≠ 0),
    ∃ i : Fin 3, v i ≠ 0 :=
  @MethbokeAddon.FDSN.exists_nonzero_coordinate

example : ∀ (p q : Frequency) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpar : ¬ FrequencyParallel p q),
    p ≠ p + q ∧ p ≠ -(p + q) ∧ q ≠ p + q ∧ q ≠ -(p + q) :=
  @MethbokeAddon.FDSN.noncollinear_triad_inputs_off_output

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) (β : ℝ → ℝ) (lambda t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) T),
    datumFourierCoeff (localizedPairVelocity a β u lambda t) =
      pairRotate a (timePhase β lambda t) (datumFourierCoeff (u t)) :=
  @MethbokeAddon.FDSN.localizedPairVelocity_coeff

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) (β : ℝ → ℝ) (lambda t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3),
    datumFourierCoeff (localizedPairVelocity a β u lambda t) a i =
      timePhase β lambda t * datumFourierCoeff (u t) a i :=
  @MethbokeAddon.FDSN.localizedPairVelocity_coeff_at

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a k : Frequency} (ha : a ≠ 0) (β : ℝ → ℝ) (lambda t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) T) (hka : k ≠ a) (hkna : k ≠ -a),
    datumFourierCoeff (localizedPairVelocity a β u lambda t) k =
      datumFourierCoeff (u t) k :=
  @MethbokeAddon.FDSN.localizedPairVelocity_coeff_off

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) (β : ℝ → ℝ) (lambda eta t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) T),
    PairSupported a
      (datumFourierCoeff (localizedPairVelocity a β u eta t) -
        datumFourierCoeff (localizedPairVelocity a β u lambda t)) :=
  @MethbokeAddon.FDSN.localizedPairVelocity_difference_pairSupported

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) {β : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) (hβt : β t = 1) (i : Fin 3)
    (hcoeff : datumFourierCoeff (u t) a i ≠ 0) {lambda eta : ℝ}
    (hlambda : |lambda| < Real.pi / 4) (heta : |eta| < Real.pi / 4)
    (hne : lambda ≠ eta),
    datumFourierCoeff (localizedPairVelocity a β u lambda t) a i ≠
      datumFourierCoeff (localizedPairVelocity a β u eta t) a i :=
  @MethbokeAddon.FDSN.localizedPairVelocity_coeff_ne_of_parameter_ne

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a k1 k2 : Frequency} (ha : a ≠ 0)
    (hk1 : k1 ≠ a) (hk1n : k1 ≠ -a) (hk2 : k2 ≠ a) (hk2n : k2 ≠ -a)
    (i1 i2 i3 : Fin 3) (β : ℝ → ℝ) (lambda t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) T),
    fieldTriadCorrelation k1 k2 a
        (coordinateObservation i1) (coordinateObservation i2) (coordinateObservation i3)
        (localizedPairVelocity a β u lambda t) =
      triadCorrelation (datumFourierCoeff (u t) k1 i1)
        (datumFourierCoeff (u t) k2 i2)
        (timePhase β lambda t * datumFourierCoeff (u t) a i3) :=
  @MethbokeAddon.FDSN.localizedPairVelocity_coordinate_triadCorrelation

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a k1 k2 : Frequency} (ha : a ≠ 0) (htriad : k1 + k2 = a)
    (hk1 : k1 ≠ a) (hk1n : k1 ≠ -a) (hk2 : k2 ≠ a) (hk2n : k2 ≠ -a)
    (i1 i2 i3 : Fin 3) {β : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) (hβt : β t = 1)
    (hB : triadCorrelation (datumFourierCoeff (u t) k1 i1)
      (datumFourierCoeff (u t) k2 i2) (datumFourierCoeff (u t) a i3) ≠ 0)
    {lambda eta : ℝ} (hlambda : |lambda| < Real.pi / 4)
    (heta : |eta| < Real.pi / 4) (hne : lambda ≠ eta),
    ¬ ∃ y : Vec, ∀ x : Vec,
      localizedPairVelocity a β u lambda t x =
        localizedPairVelocity a β u eta t (x + y) :=
  @MethbokeAddon.FDSN.localizedPairVelocity_not_translation

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T)
    (hactive : HasActiveNoncollinearTriad (datumFourierCoeff (u t))),
    ∃ a : Frequency, a ≠ 0 ∧ ∃ i : Fin 3,
      datumFourierCoeff (u t) a i ≠ 0 ∧
      ∀ β : ℝ → ℝ, β t = 1 → ∀ lambda eta : ℝ,
        |lambda| < Real.pi / 4 → |eta| < Real.pi / 4 → lambda ≠ eta →
        (datumFourierCoeff (localizedPairVelocity a β u lambda t) a i ≠
          datumFourierCoeff (localizedPairVelocity a β u eta t) a i) ∧
        ¬ ∃ y : Vec, ∀ x : Vec,
          localizedPairVelocity a β u lambda t x =
            localizedPairVelocity a β u eta t (x + y) :=
  @MethbokeAddon.FDSN.Seed.active_triad_separation_data

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.coordinateObservation"
#check @MethbokeAddon.FDSN.coordinateObservation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.coordinateObservation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.coordinateObservation"
#print axioms MethbokeAddon.FDSN.coordinateObservation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.coordinateObservation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.exists_nonzero_coordinate"
#check @MethbokeAddon.FDSN.exists_nonzero_coordinate
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.exists_nonzero_coordinate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.exists_nonzero_coordinate"
#print axioms MethbokeAddon.FDSN.exists_nonzero_coordinate
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.exists_nonzero_coordinate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.noncollinear_triad_inputs_off_output"
#check @MethbokeAddon.FDSN.noncollinear_triad_inputs_off_output
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.noncollinear_triad_inputs_off_output"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.noncollinear_triad_inputs_off_output"
#print axioms MethbokeAddon.FDSN.noncollinear_triad_inputs_off_output
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.noncollinear_triad_inputs_off_output"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_coeff"
#check @MethbokeAddon.FDSN.localizedPairVelocity_coeff
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_coeff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_coeff"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_coeff
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_coeff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_coeff_at"
#check @MethbokeAddon.FDSN.localizedPairVelocity_coeff_at
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_coeff_at"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_coeff_at"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_coeff_at
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_coeff_at"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_coeff_off"
#check @MethbokeAddon.FDSN.localizedPairVelocity_coeff_off
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_coeff_off"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_coeff_off"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_coeff_off
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_coeff_off"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_difference_pairSupported"
#check @MethbokeAddon.FDSN.localizedPairVelocity_difference_pairSupported
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_difference_pairSupported"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_difference_pairSupported"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_difference_pairSupported
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_difference_pairSupported"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_coeff_ne_of_parameter_ne"
#check @MethbokeAddon.FDSN.localizedPairVelocity_coeff_ne_of_parameter_ne
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_coeff_ne_of_parameter_ne"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_coeff_ne_of_parameter_ne"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_coeff_ne_of_parameter_ne
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_coeff_ne_of_parameter_ne"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_coordinate_triadCorrelation"
#check @MethbokeAddon.FDSN.localizedPairVelocity_coordinate_triadCorrelation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_coordinate_triadCorrelation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_coordinate_triadCorrelation"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_coordinate_triadCorrelation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_coordinate_triadCorrelation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_not_translation"
#check @MethbokeAddon.FDSN.localizedPairVelocity_not_translation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_not_translation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_not_translation"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_not_translation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_not_translation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.Seed.active_triad_separation_data"
#check @MethbokeAddon.FDSN.Seed.active_triad_separation_data
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.Seed.active_triad_separation_data"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.Seed.active_triad_separation_data"
#print axioms MethbokeAddon.FDSN.Seed.active_triad_separation_data
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.Seed.active_triad_separation_data"

