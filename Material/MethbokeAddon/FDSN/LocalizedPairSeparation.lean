import MethbokeAddon.FDSN.LocalizedPair
import MethbokeAddon.FDSN.PairForceUniqueness
import MethbokeAddon.FDSN.FourierTranslation

/-!
# Concrete Fourier and translation separation of the localized pair family

An active vector triad supplies nonzero Cartesian coordinates. Its input
frequencies lie outside the rotated output pair, so its actual Fourier
correlation acquires exactly the selected scalar phase. No helical basis
is required for this nontranslation certificate.
-/

set_option autoImplicit false

noncomputable section
open Set SingularClosure
open scoped BigOperators ContDiff Topology

namespace MethbokeAddon.FDSN

def coordinateObservation (i : Fin 3) : (Fin 3 → ℂ) →ₗ[ℂ] ℂ where
  toFun v := v i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_nonzero_coordinate {v : Fin 3 → ℂ} (hv : v ≠ 0) :
    ∃ i : Fin 3, v i ≠ 0 := by
  classical
  by_contra hnone
  apply hv
  funext i
  by_contra hi
  exact hnone ⟨i, hi⟩

/-- In a noncollinear nonzero triad, neither input can be either member
of the output conjugate pair. -/
theorem noncollinear_triad_inputs_off_output
    (p q : Frequency) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpar : ¬ FrequencyParallel p q) :
    p ≠ p + q ∧ p ≠ -(p + q) ∧ q ≠ p + q ∧ q ≠ -(p + q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro he
    apply hq
    funext j
    have hj := congrFun he j
    change p j = p j + q j at hj
    change q j = 0
    omega
  · intro he
    apply hpar
    refine ⟨-2, ?_⟩
    intro j
    have hj := congrFun he j
    change p j = -(p j + q j) at hj
    have hqj : q j = -2 * p j := by omega
    exact_mod_cast hqj
  · intro he
    apply hp
    funext j
    have hj := congrFun he j
    change q j = p j + q j at hj
    change p j = 0
    omega
  · intro he
    apply hpar
    refine ⟨-(1 / 2 : ℝ), ?_⟩
    intro j
    have hj := congrFun he j
    change q j = -(p j + q j) at hj
    have hpj : p j = -2 * q j := by omega
    have hpjR : (p j : ℝ) = -2 * (q j : ℝ) := by exact_mod_cast hpj
    linarith

theorem localizedPairVelocity_coeff
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) (β : ℝ → ℝ) (lambda t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) T) :
    datumFourierCoeff (localizedPairVelocity a β u lambda t) =
      pairRotate a (timePhase β lambda t) (datumFourierCoeff (u t)) := by
  rw [localizedPairVelocity_eq_physicalPairRotation h ha β lambda t ht]
  exact physicalPairRotation_coeff ha (norm_timePhase β lambda t)
    (h.velocity_slice_smooth t ht) (h.front.velocity_periodic t ht)

theorem localizedPairVelocity_coeff_at
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) (β : ℝ → ℝ) (lambda t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3) :
    datumFourierCoeff (localizedPairVelocity a β u lambda t) a i =
      timePhase β lambda t * datumFourierCoeff (u t) a i := by
  rw [localizedPairVelocity_coeff h ha β lambda t ht, pairRotate_at]
  rfl

theorem localizedPairVelocity_coeff_off
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a k : Frequency} (ha : a ≠ 0) (β : ℝ → ℝ) (lambda t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) T) (hka : k ≠ a) (hkna : k ≠ -a) :
    datumFourierCoeff (localizedPairVelocity a β u lambda t) k =
      datumFourierCoeff (u t) k := by
  rw [localizedPairVelocity_coeff h ha β lambda t ht]
  exact pairRotate_off _ _ hka hkna

theorem localizedPairVelocity_difference_pairSupported
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) (β : ℝ → ℝ) (lambda eta t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) T) :
    PairSupported a
      (datumFourierCoeff (localizedPairVelocity a β u eta t) -
        datumFourierCoeff (localizedPairVelocity a β u lambda t)) := by
  intro k hka hkna
  change datumFourierCoeff (localizedPairVelocity a β u eta t) k -
    datumFourierCoeff (localizedPairVelocity a β u lambda t) k = 0
  rw [localizedPairVelocity_coeff_off h ha β eta t ht hka hkna,
    localizedPairVelocity_coeff_off h ha β lambda t ht hka hkna, sub_self]

theorem localizedPairVelocity_coeff_ne_of_parameter_ne
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) {β : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) (hβt : β t = 1) (i : Fin 3)
    (hcoeff : datumFourierCoeff (u t) a i ≠ 0) {lambda eta : ℝ}
    (hlambda : |lambda| < Real.pi / 4) (heta : |eta| < Real.pi / 4)
    (hne : lambda ≠ eta) :
    datumFourierCoeff (localizedPairVelocity a β u lambda t) a i ≠
      datumFourierCoeff (localizedPairVelocity a β u eta t) a i := by
  rw [localizedPairVelocity_coeff_at h ha β lambda t ht i,
    localizedPairVelocity_coeff_at h ha β eta t ht i,
    timePhase_at_normalization hβt, timePhase_at_normalization hβt]
  intro he
  exact hne (phase_injective_small hlambda heta (mul_right_cancel₀ hcoeff he))

theorem localizedPairVelocity_coordinate_triadCorrelation
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a k1 k2 : Frequency} (ha : a ≠ 0)
    (hk1 : k1 ≠ a) (hk1n : k1 ≠ -a) (hk2 : k2 ≠ a) (hk2n : k2 ≠ -a)
    (i1 i2 i3 : Fin 3) (β : ℝ → ℝ) (lambda t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) T) :
    fieldTriadCorrelation k1 k2 a
        (coordinateObservation i1) (coordinateObservation i2) (coordinateObservation i3)
        (localizedPairVelocity a β u lambda t) =
      triadCorrelation (datumFourierCoeff (u t) k1 i1)
        (datumFourierCoeff (u t) k2 i2)
        (timePhase β lambda t * datumFourierCoeff (u t) a i3) := by
  change triadCorrelation
    (datumFourierCoeff (localizedPairVelocity a β u lambda t) k1 i1)
    (datumFourierCoeff (localizedPairVelocity a β u lambda t) k2 i2)
    (datumFourierCoeff (localizedPairVelocity a β u lambda t) a i3) = _
  rw [localizedPairVelocity_coeff_off h ha β lambda t ht hk1 hk1n,
    localizedPairVelocity_coeff_off h ha β lambda t ht hk2 hk2n,
    localizedPairVelocity_coeff_at h ha β lambda t ht i3]

/-- Pairwise nontranslation at the common normalized time, in the literal
orientation used by the family contract. -/
theorem localizedPairVelocity_not_translation
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a k1 k2 : Frequency} (ha : a ≠ 0) (htriad : k1 + k2 = a)
    (hk1 : k1 ≠ a) (hk1n : k1 ≠ -a) (hk2 : k2 ≠ a) (hk2n : k2 ≠ -a)
    (i1 i2 i3 : Fin 3) {β : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) (hβt : β t = 1)
    (hB : triadCorrelation (datumFourierCoeff (u t) k1 i1)
      (datumFourierCoeff (u t) k2 i2) (datumFourierCoeff (u t) a i3) ≠ 0)
    {lambda eta : ℝ} (hlambda : |lambda| < Real.pi / 4)
    (heta : |eta| < Real.pi / 4) (hne : lambda ≠ eta) :
    ¬ ∃ y : Vec, ∀ x : Vec,
      localizedPairVelocity a β u lambda t x =
        localizedPairVelocity a β u eta t (x + y) := by
  have hdata := LOCALIZED_PAIR_VELOCITY_PRESERVES_SPECTRAL_DATA h ha β eta t ht
  have hcor : fieldTriadCorrelation k1 k2 a
        (coordinateObservation i1) (coordinateObservation i2) (coordinateObservation i3)
        (localizedPairVelocity a β u eta t) ≠
      fieldTriadCorrelation k1 k2 a
        (coordinateObservation i1) (coordinateObservation i2) (coordinateObservation i3)
        (localizedPairVelocity a β u lambda t) := by
    rw [localizedPairVelocity_coordinate_triadCorrelation h ha hk1 hk1n hk2 hk2n
      i1 i2 i3 β eta t ht,
      localizedPairVelocity_coordinate_triadCorrelation h ha hk1 hk1n hk2 hk2n
      i1 i2 i3 β lambda t ht]
    exact timePhase_triad_separates hβt hB heta hlambda hne.symm
  have hnot := fields_not_translation_of_triadCorrelation_ne k1 k2 a htriad
    (coordinateObservation i1) (coordinateObservation i2) (coordinateObservation i3)
    (localizedPairVelocity a β u eta t) (localizedPairVelocity a β u lambda t)
    hdata.1 hdata.2.1 hcor
  rintro ⟨y, hy⟩
  exact hnot ⟨y, fun x => (hy x).symm⟩

/-- An actual active vector triad chooses one Fourier pair and one nonzero
coordinate that separate every small distinct pair of phase parameters. -/
theorem Seed.active_triad_separation_data
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T)
    (hactive : HasActiveNoncollinearTriad (datumFourierCoeff (u t))) :
    ∃ a : Frequency, a ≠ 0 ∧ ∃ i : Fin 3,
      datumFourierCoeff (u t) a i ≠ 0 ∧
      ∀ β : ℝ → ℝ, β t = 1 → ∀ lambda eta : ℝ,
        |lambda| < Real.pi / 4 → |eta| < Real.pi / 4 → lambda ≠ eta →
        (datumFourierCoeff (localizedPairVelocity a β u lambda t) a i ≠
          datumFourierCoeff (localizedPairVelocity a β u eta t) a i) ∧
        ¬ ∃ y : Vec, ∀ x : Vec,
          localizedPairVelocity a β u lambda t x =
            localizedPairVelocity a β u eta t (x + y) := by
  obtain ⟨k1, k2, hk1, hk2, ha, hc1, hc2, hc3, hpar⟩ := hactive
  obtain ⟨i1, hi1⟩ := exists_nonzero_coordinate hc1
  obtain ⟨i2, hi2⟩ := exists_nonzero_coordinate hc2
  obtain ⟨i3, hi3⟩ := exists_nonzero_coordinate hc3
  obtain ⟨h1, h1n, h2, h2n⟩ := noncollinear_triad_inputs_off_output k1 k2 hk1 hk2 hpar
  refine ⟨k1 + k2, ha, i3, hi3, ?_⟩
  intro β hβt lambda eta hlambda heta hne
  exact ⟨localizedPairVelocity_coeff_ne_of_parameter_ne h ha ht hβt i3 hi3
      hlambda heta hne,
    localizedPairVelocity_not_translation h ha rfl h1 h1n h2 h2n i1 i2 i3
      ht hβt (triadCorrelation_ne_zero hi1 hi2 hi3) hlambda heta hne⟩

end MethbokeAddon.FDSN
