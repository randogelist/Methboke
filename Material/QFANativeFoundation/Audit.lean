import QFANativeFoundation.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

namespace QFANativeFoundation.ContractTypeChecks

-- Passive external-audit fragment for the two native contract/energy files.
-- Prepared statically; never executed locally. Root may incorporate it into
-- QFANativeFoundation/Audit.lean and its named axiom-audit manifest.


set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Interval Topology
open MethbokeAddon.QuasiFeffermanA

-- Literal carrier and differential-operator checks.
example : Space = EuclideanSpace ℝ (Fin 3) := rfl
example : SpatialL2 =
    Lp (EuclideanSpace ℝ (Fin 3)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : Velocity = (ℝ → SpatialL2) := rfl
example : WeakGradient = (ℝ → Fin 3 → SpatialL2) := rfl
example (j : Fin 3) : coordinateVector j = EuclideanSpace.single j 1 := rfl
example (ψ : Space → ℝ) (x : Space) :
    scalarGradient ψ x =
      WithLp.toLp 2 (fun j : Fin 3 => fderiv ℝ ψ x (EuclideanSpace.single j 1)) := rfl
example : EnergyDatum = {a : SpatialL2 // Solenoidal a} := rfl

-- All scalar compact tests, literal full-volume pairings, with integrability.
example (v : SpatialL2) :
    Solenoidal v ↔
      ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        Integrable (fun x : Space => inner ℝ (v x)
          (WithLp.toLp 2 (fun j : Fin 3 =>
            fderiv ℝ ψ x (EuclideanSpace.single j 1)))) volume ∧
        (∫ x : Space, inner ℝ (v x)
          (WithLp.toLp 2 (fun j : Fin 3 =>
            fderiv ℝ ψ x (EuclideanSpace.single j 1)))) = 0 := Iff.rfl

-- Each coordinate is an actual weak directional derivative against every
-- real smooth compact scalar test. Neither a finite test set nor a semantic
-- derivative predicate is substituted here.
example (v : SpatialL2) (G : Fin 3 → SpatialL2) :
    SpatialWeakGradient v G ↔
      ∀ (j : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ x : Space, (fderiv ℝ ψ x (EuclideanSpace.single j 1)) • v x) =
          -(∫ x : Space, ψ x • G j x) := Iff.rfl

-- Both directions of the concrete momentum-test contract.
example (φ : MomentumTest) :
    ContDiff ℝ ∞ φ.value ∧ HasCompactSupport φ.value ∧
      tsupport φ.value ⊆ {z : ℝ × Space | 0 < z.1} ∧
      ∀ (t : ℝ) (x : Space),
        (∑ j : Fin 3,
          (fderiv ℝ (fun y : Space => φ.value (t, y)) x
            (EuclideanSpace.single j 1)) j) = 0 :=
  ⟨φ.smooth, φ.compact_support, φ.positive_support, φ.solenoidal⟩

example (φ : ℝ × Space → Space)
    (hsmooth : ContDiff ℝ ∞ φ) (hcompact : HasCompactSupport φ)
    (hpositive : tsupport φ ⊆ {z : ℝ × Space | 0 < z.1})
    (hdiv : ∀ (t : ℝ) (x : Space),
      (∑ j : Fin 3,
        (fderiv ℝ (fun y : Space => φ (t, y)) x
          (EuclideanSpace.single j 1)) j) = 0) : MomentumTest :=
  ⟨φ, hsmooth, hcompact, hpositive, hdiv⟩

-- The three contractions, including the viscosity sign in the equation below.
example (u : Velocity) (φ : MomentumTest) (t : ℝ) (x : Space) :
    momentumTimeIntegrand u φ t x =
      inner ℝ (u t x) (fderiv ℝ (fun r : ℝ => φ.value (r, x)) t 1) := rfl
example (u : Velocity) (φ : MomentumTest) (t : ℝ) (x : Space) :
    momentumConvectionIntegrand u φ t x =
      ∑ j : Fin 3, (u t x) j * inner ℝ (u t x)
        (fderiv ℝ (fun y : Space => φ.value (t, y)) x
          (EuclideanSpace.single j 1)) := rfl
example (G : WeakGradient) (φ : MomentumTest) (t : ℝ) (x : Space) :
    momentumDissipationIntegrand G φ t x =
      ∑ j : Fin 3, inner ℝ (G t j x)
        (fderiv ℝ (fun y : Space => φ.value (t, y)) x
          (EuclideanSpace.single j 1)) := rfl

-- This literal expansion also rules out extra hidden fields in WeakMomentum.
example (ν : ℝ) (u : Velocity) (G : WeakGradient) :
    WeakMomentum ν u G ↔
      (∀ (φ : MomentumTest) (t : ℝ), 0 ≤ t →
        Integrable (momentumTimeIntegrand u φ t) volume ∧
          Integrable (momentumConvectionIntegrand u φ t) volume ∧
          Integrable (momentumDissipationIntegrand G φ t) volume) ∧
      (∀ φ : MomentumTest,
        Integrable (fun t : ℝ => ∫ x : Space, momentumTimeIntegrand u φ t x)
            (volume.restrict (Ioi (0 : ℝ))) ∧
          Integrable (fun t : ℝ => ∫ x : Space, momentumConvectionIntegrand u φ t x)
            (volume.restrict (Ioi (0 : ℝ))) ∧
          Integrable (fun t : ℝ => ∫ x : Space, momentumDissipationIntegrand G φ t x)
            (volume.restrict (Ioi (0 : ℝ)))) ∧
      (∀ φ : MomentumTest,
        (∫ t in Ioi (0 : ℝ), ∫ x : Space, momentumTimeIntegrand u φ t x) +
            (∫ t in Ioi (0 : ℝ), ∫ x : Space, momentumConvectionIntegrand u φ t x) -
            ν * (∫ t in Ioi (0 : ℝ), ∫ x : Space, momentumDissipationIntegrand G φ t x) = 0) := by
  constructor
  · intro h
    exact ⟨h.spatial_integrability, h.time_integrability, h.equation⟩
  · rintro ⟨hspace, htime, heq⟩
    exact ⟨hspace, htime, heq⟩

example (ν s : ℝ) (u : Velocity) (G : WeakGradient) :
    EnergyStart ν u G s ↔
      ∀ r : ℝ, s ≤ r →
        ‖u r‖ ^ 2 + 2 * ν * (∫ q in s..r, ∑ j : Fin 3, ‖G q j‖ ^ 2) ≤
          ‖u s‖ ^ 2 := Iff.rfl

-- Full LH literal field list. Strong traces are absent from the assumptions;
-- they are proved below. No constructor, comparison, smoothness, existence,
-- cutoff or continuation field can be hidden in this equivalence.
example (ν : ℝ) (a : SpatialL2) (u : Velocity) (G : WeakGradient) :
    LerayHopf ν a u G ↔
      WeakMomentum ν u G ∧
      u 0 = a ∧
      (∀ t : ℝ, 0 ≤ t → Solenoidal (u t)) ∧
      (∀ R : ℝ, 0 < R →
        AEStronglyMeasurable u (volume.restrict (Ioo (0 : ℝ) R))) ∧
      (∀ R : ℝ, 0 < R → ∀ j : Fin 3,
        MemLp (fun t => G t j) 2 (volume.restrict (Ioo (0 : ℝ) R))) ∧
      (∀ R : ℝ, 0 < R →
        ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R), SpatialWeakGradient (u t) (G t)) ∧
      (∀ b : SpatialL2,
        ContinuousOn (fun t => inner ℝ (u t) b) (Ici (0 : ℝ))) ∧
      (∀ t : ℝ, 0 ≤ t →
        ‖u t‖ ^ 2 + 2 * ν * (∫ r in (0 : ℝ)..t, ∑ j : Fin 3, ‖G r j‖ ^ 2) ≤
          ‖a‖ ^ 2) ∧
      (∀ R : ℝ, 0 < R →
        ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) R),
          ∀ r : ℝ, s ≤ r →
            ‖u r‖ ^ 2 + 2 * ν * (∫ q in s..r, ∑ j : Fin 3, ‖G q j‖ ^ 2) ≤
              ‖u s‖ ^ 2) := by
  constructor
  · intro h
    exact ⟨h.momentum, h.initial, h.solenoidal, h.velocity_aestronglyMeasurable,
      h.gradient_memLp, h.spatial_weak_gradient, h.weak_continuity,
      h.energy_initial, h.energy_starts⟩
  · rintro ⟨hmom, hinitial, hsol, hmeas, hmem, hgradient, hweak, henergy, hstarts⟩
    exact ⟨hmom, hinitial, hsol, hmeas, hmem, hgradient, hweak, henergy, hstarts⟩

-- Independent full-type consumers for every new theorem.
example {ν s : ℝ} {u : Velocity} {G : WeakGradient} :
    EnergyStart ν u G s ↔ QFA.Assembly.Restart.EnergyStart ν u G s :=
  energyStart_iff_qfa

example {ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) : QFA.Representation.EnergyProfile ν a u G :=
  LerayHopf.energyProfile h

example {ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) : Solenoidal a :=
  LerayHopf.initial_solenoidal h

example {ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) :
    ‖u t‖ ^ 2 ≤ ‖a‖ ^ 2 :=
  LerayHopf.velocity_energy_le_initial h hν ht

example {ν R : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 < ν) (hR : 0 < R) :
    Integrable (fun t => ‖u t‖ ^ 2 * (∑ j : Fin 3, ‖G t j‖ ^ 2))
        (volume.restrict (Ioo (0 : ℝ) R)) ∧
      (∫ t in Ioo (0 : ℝ) R, ‖u t‖ ^ 2 * (∑ j : Fin 3, ‖G t j‖ ^ 2)) ≤
        ‖a‖ ^ 4 / (4 * ν) :=
  LerayHopf.energy_product_budget_Ioo h hν hR

example {ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) :
    ∀ r : ℝ, 0 ≤ r →
      ‖u r‖ ^ 2 + 2 * ν * (∫ q in (0 : ℝ)..r, ∑ j : Fin 3, ‖G q j‖ ^ 2) ≤
        ‖u 0‖ ^ 2 :=
  LerayHopf.energyStart_zero h

example {ν s : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) (hs : 0 ≤ s)
    (hstart : ∀ r : ℝ, s ≤ r →
      ‖u r‖ ^ 2 + 2 * ν * (∫ q in s..r, ∑ j : Fin 3, ‖G q j‖ ^ 2) ≤
        ‖u s‖ ^ 2) :
    Tendsto u (𝓝[>] s) (𝓝 (u s)) :=
  LerayHopf.strong_right_trace h hν hs hstart

example {ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) :
    Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a) :=
  LerayHopf.strong_initial_trace h hν

example {ν s : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) (hs : 0 ≤ s)
    (hstart : ∀ r : ℝ, s ≤ r →
      ‖u r‖ ^ 2 + 2 * ν * (∫ q in s..r, ∑ j : Fin 3, ‖G q j‖ ^ 2) ≤
        ‖u s‖ ^ 2) :
    QFA.Assembly.Restart.RestartData ν u G s :=
  LerayHopf.restart_energy_data h hν hs hstart

example {ν R : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) (hR : 0 < R) :
    ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) R),
      Solenoidal (u s) ∧ SpatialWeakGradient (u s) (G s) ∧
        EnergyStart ν u G s ∧ QFA.Assembly.Restart.RestartData ν u G s :=
  LerayHopf.ae_restart_energy_data h hν hR

example {ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) (ha : a = 0)
    {t : ℝ} (ht : 0 ≤ t) : u t = 0 :=
  LerayHopf.eq_zero_of_initial_eq_zero h hν ha ht


end
end QFANativeFoundation.ContractTypeChecks

namespace QFANativeFoundation.CutoffTypeChecks


/- Independent expected-type consumers for the prepared scalar layer.
   This text is passive and has not been compiled locally. The integration
   owner supplies exact-name sentinels and fresh external axiom audits. -/

set_option autoImplicit false

open Set MeasureTheory MethbokeAddon.QuasiFeffermanA
open scoped Interval

noncomputable section

-- Literal definition consumers, including the order of the scalar arguments.
example (S ν : ℝ) : productThreshold S ν = ν ^ 4 / S ^ 6 := rfl

example (S M ν : ℝ) : safeCutoff S M ν = S ^ 6 * M ^ 4 / (2 * ν ^ 5) := rfl

example : ∀ {S ν : ℝ}, 0 < S → 0 < ν → 0 < productThreshold S ν :=
  @MethbokeAddon.QuasiFeffermanA.productThreshold_pos

example : ∀ (S M : ℝ) {ν : ℝ}, 0 < ν → 0 ≤ safeCutoff S M ν :=
  @MethbokeAddon.QuasiFeffermanA.safeCutoff_nonneg

example : ∀ {S M ν : ℝ},
    0 < S → 0 < ν → M ≠ 0 → 0 < safeCutoff S M ν :=
  @MethbokeAddon.QuasiFeffermanA.safeCutoff_pos

example : ∀ S ν : ℝ, safeCutoff S 0 ν = 0 :=
  @MethbokeAddon.QuasiFeffermanA.safeCutoff_zero

example : ∀ {S M ν : ℝ}, 0 < S → 0 < ν →
    productThreshold S ν * safeCutoff S M ν = M ^ 4 / (2 * ν) :=
  @MethbokeAddon.QuasiFeffermanA.threshold_mul_safeCutoff

example : ∀ {S M ν : ℝ}, 0 < S → 0 < ν →
    M ^ 4 / (4 * ν) = productThreshold S ν * safeCutoff S M ν / 2 :=
  @MethbokeAddon.QuasiFeffermanA.budget_eq_half_threshold_cutoff

example : ∀ {S M ν : ℝ}, 0 < S → 0 < ν → M ≠ 0 →
    M ^ 4 / (4 * ν) < productThreshold S ν * safeCutoff S M ν :=
  @MethbokeAddon.QuasiFeffermanA.budget_lt_threshold_cutoff

example : ∀ {S M ν : ℝ}, 0 < ν → S ^ 6 = 16 / (27 * Real.pi ^ 4) →
    safeCutoff S M ν = 8 * M ^ 4 / (27 * Real.pi ^ 4 * ν ^ 5) :=
  @MethbokeAddon.QuasiFeffermanA.safeCutoff_eq_pi_formula_of_sixth_power

example : ∀ {E D : ℝ → ℝ} {Good : ℝ → Prop} {S M ν : ℝ},
    0 < S → 0 < ν → M ≠ 0 →
    Integrable (fun t => E t * D t)
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν))) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), Good t) →
    (∫ t in Ioo (0 : ℝ) (safeCutoff S M ν), E t * D t) ≤ M ^ 4 / (4 * ν) →
    ∃ s, 0 < s ∧ s < safeCutoff S M ν ∧ Good s ∧
      E s * D s < productThreshold S ν :=
  @MethbokeAddon.QuasiFeffermanA.exists_good_time_of_product_budget

example : ∀ {E D : ℝ → ℝ} {Good : ℝ → Prop} {S M ν : ℝ},
    0 < S → 0 < ν → M ≠ 0 →
    IntervalIntegrable D volume (0 : ℝ) (safeCutoff S M ν) →
    AEStronglyMeasurable E
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν))) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), 0 ≤ D t) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), 0 ≤ E t) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)),
      E t ≤ QFA.Energy.envelope M ν D t) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), Good t) →
    ∃ s, 0 < s ∧ s < safeCutoff S M ν ∧ Good s ∧
      E s * D s < productThreshold S ν :=
  @MethbokeAddon.QuasiFeffermanA.exists_good_time_of_energy_envelope

example : ∀ {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} {c : ℝ},
    0 < c → Integrable f μ → (∀ᵐ x ∂μ, 0 ≤ f x) →
    (∫ x, f x ∂μ) ≤ c * μ.real univ / 2 →
    μ.real univ / 2 ≤ μ.real {x | f x < c} :=
  @MethbokeAddon.QuasiFeffermanA.subcritical_measure_ge_half

example : ∀ {E D : ℝ → ℝ} {Good : ℝ → Prop} {S M ν : ℝ},
    0 < S → 0 < ν →
    Integrable (fun t => E t * D t)
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν))) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), 0 ≤ E t * D t) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), Good t) →
    (∫ t in Ioo (0 : ℝ) (safeCutoff S M ν), E t * D t) ≤ M ^ 4 / (4 * ν) →
    safeCutoff S M ν / 2 ≤
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν))).real
        {t | Good t ∧ E t * D t < productThreshold S ν} :=
  @MethbokeAddon.QuasiFeffermanA.good_set_measure_ge_half_of_product_budget

example : ∀ {E D : ℝ → ℝ} {Good : ℝ → Prop} {S M ν : ℝ},
    0 < S → 0 < ν → M ≠ 0 →
    IntervalIntegrable D volume (0 : ℝ) (safeCutoff S M ν) →
    AEStronglyMeasurable E
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν))) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), 0 ≤ D t) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), 0 ≤ E t) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)),
      E t ≤ QFA.Energy.envelope M ν D t) →
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν)), Good t) →
    (safeCutoff S M ν / 2 ≤
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S M ν))).real
        {t | Good t ∧ E t * D t < productThreshold S ν}) ∧
      ∃ s, 0 < s ∧ s < safeCutoff S M ν ∧ Good s ∧
        E s * D s < productThreshold S ν :=
  @MethbokeAddon.QuasiFeffermanA.good_time_and_measure_of_energy_envelope

end

end QFANativeFoundation.CutoffTypeChecks

namespace QFANativeFoundation.SpectralTypeChecks


set_option autoImplicit false
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

-- Independent complete signatures: no norm-density or spectral input is assumed.
example : ∀ {v : QFA.Endpoints.Agmon.ComplexL2}
    {G : Fin 3 → QFA.Endpoints.Agmon.ComplexL2}
    {L : QFA.Endpoints.Agmon.ComplexL2},
    QFA.Endpoints.Agmon.SchwartzDerivativeWitnesses v G L →
      QFA.LC001SpectralReduction.FourierNormAEWitnesses v G L :=
  @MethbokeAddon.QuasiFeffermanA.fourierNormAEWitnesses_of_schwartzDerivativeWitnesses

example : ∀ {v : QFA.Endpoints.Agmon.ComplexL2}
    {G : Fin 3 → QFA.Endpoints.Agmon.ComplexL2}
    {L : QFA.Endpoints.Agmon.ComplexL2},
    QFA.Endpoints.Agmon.SchwartzDerivativeWitnesses v G L →
      QFA.Endpoints.Agmon.NativeSpectralRealization v G L :=
  @MethbokeAddon.QuasiFeffermanA.nativeSpectralRealization_of_schwartzDerivativeWitnesses

-- The endpoint abbreviation is expanded in this consumer.
example : ∀ (v : QFA.Endpoints.Agmon.ComplexL2)
    (G : Fin 3 → QFA.Endpoints.Agmon.ComplexL2)
    (L : QFA.Endpoints.Agmon.ComplexL2),
    QFA.Endpoints.Agmon.SchwartzDerivativeWitnesses v G L →
      QFA.Endpoints.Agmon.NativeSpectralRealization v G L :=
  MethbokeAddon.QuasiFeffermanA.wholeSpaceSpectralEndpoint


end QFANativeFoundation.SpectralTypeChecks

namespace QFANativeFoundation.FourierMultiplierTypeChecks


set_option autoImplicit false
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap

namespace QFAFourierMultipliersIndependentConsumers

-- Each independent consumer states every hypothesis and the full conclusion.
example (q h : QFA.Endpoints.Agmon.ComplexL2) (c : ℂ)
    (m : QFA.Endpoints.Agmon.Space → ℝ)
    (hm_cont : Continuous m) (hm_temp : m.HasTemperateGrowth)
    (hEq : (q : 𝓢'(QFA.Endpoints.Agmon.Space, QFA.Endpoints.Agmon.ComplexVector)) =
      c • TemperedDistribution.smulLeftCLM QFA.Endpoints.Agmon.ComplexVector
        (fun x : QFA.Endpoints.Agmon.Space => (m x : ℂ))
        (h : 𝓢'(QFA.Endpoints.Agmon.Space, QFA.Endpoints.Agmon.ComplexVector))) :
    (fun x : QFA.Endpoints.Agmon.Space => q x) =ᵐ[volume]
      (fun x : QFA.Endpoints.Agmon.Space => (c * (m x : ℂ)) • h x) :=
  MethbokeAddon.QuasiFeffermanA.FourierMultipliers.ae_eq_of_const_smul_real_multiplier_distribution
    q h c m hm_cont hm_temp hEq

example {v : QFA.Endpoints.Agmon.ComplexL2}
    {G : Fin 3 → QFA.Endpoints.Agmon.ComplexL2}
    {L : QFA.Endpoints.Agmon.ComplexL2}
    (h : QFA.Endpoints.Agmon.SchwartzDerivativeWitnesses v G L) (j : Fin 3) :
    ((𝓕 (G j) : QFA.Endpoints.Agmon.ComplexL2) :
        𝓢'(QFA.Endpoints.Agmon.Space, QFA.Endpoints.Agmon.ComplexVector)) =
      (2 * Real.pi * Complex.I) •
        TemperedDistribution.smulLeftCLM QFA.Endpoints.Agmon.ComplexVector
          (fun x : QFA.Endpoints.Agmon.Space =>
            (inner ℝ x (EuclideanSpace.basisFun (Fin 3) ℝ j) : ℂ))
          ((𝓕 v : QFA.Endpoints.Agmon.ComplexL2) :
            𝓢'(QFA.Endpoints.Agmon.Space, QFA.Endpoints.Agmon.ComplexVector)) :=
  MethbokeAddon.QuasiFeffermanA.FourierMultipliers.gradient_fourier_distribution_eq h j

example {v : QFA.Endpoints.Agmon.ComplexL2}
    {G : Fin 3 → QFA.Endpoints.Agmon.ComplexL2}
    {L : QFA.Endpoints.Agmon.ComplexL2}
    (h : QFA.Endpoints.Agmon.SchwartzDerivativeWitnesses v G L) (j : Fin 3) :
    (fun k : QFA.Endpoints.Agmon.Space => (𝓕 (G j) : QFA.Endpoints.Agmon.ComplexL2) k)
      =ᵐ[volume]
        (fun k : QFA.Endpoints.Agmon.Space =>
          ((2 * Real.pi * Complex.I) *
            (inner ℝ k (EuclideanSpace.basisFun (Fin 3) ℝ j) : ℂ)) •
              (𝓕 v : QFA.Endpoints.Agmon.ComplexL2) k) :=
  MethbokeAddon.QuasiFeffermanA.FourierMultipliers.gradient_fourier_ae h j

example {v : QFA.Endpoints.Agmon.ComplexL2}
    {G : Fin 3 → QFA.Endpoints.Agmon.ComplexL2}
    {L : QFA.Endpoints.Agmon.ComplexL2}
    (h : QFA.Endpoints.Agmon.SchwartzDerivativeWitnesses v G L) :
    ((𝓕 L : QFA.Endpoints.Agmon.ComplexL2) :
        𝓢'(QFA.Endpoints.Agmon.Space, QFA.Endpoints.Agmon.ComplexVector)) =
      (-((2 * Real.pi) ^ 2)) •
        TemperedDistribution.smulLeftCLM QFA.Endpoints.Agmon.ComplexVector
          (fun k : QFA.Endpoints.Agmon.Space => (‖k‖ ^ 2 : ℂ))
          ((𝓕 v : QFA.Endpoints.Agmon.ComplexL2) :
            𝓢'(QFA.Endpoints.Agmon.Space, QFA.Endpoints.Agmon.ComplexVector)) :=
  MethbokeAddon.QuasiFeffermanA.FourierMultipliers.laplacian_fourier_distribution_eq h

example {v : QFA.Endpoints.Agmon.ComplexL2}
    {G : Fin 3 → QFA.Endpoints.Agmon.ComplexL2}
    {L : QFA.Endpoints.Agmon.ComplexL2}
    (h : QFA.Endpoints.Agmon.SchwartzDerivativeWitnesses v G L) :
    (fun k : QFA.Endpoints.Agmon.Space => (𝓕 L : QFA.Endpoints.Agmon.ComplexL2) k)
      =ᵐ[volume]
        (fun k : QFA.Endpoints.Agmon.Space =>
          ((-((2 * Real.pi) ^ 2) : ℂ) * (‖k‖ ^ 2 : ℂ)) •
            (𝓕 v : QFA.Endpoints.Agmon.ComplexL2) k) :=
  MethbokeAddon.QuasiFeffermanA.FourierMultipliers.laplacian_fourier_ae h

end QFAFourierMultipliersIndependentConsumers


end QFANativeFoundation.FourierMultiplierTypeChecks

namespace QFANativeFoundation.IntegrationTypeChecks

open MeasureTheory Set Filter MethbokeAddon.QuasiFeffermanA
open scoped Topology BigOperators

example (ν s : ℝ) (u : Velocity) (G : WeakGradient) :
    GoodRestart ν u G s ↔
      Solenoidal (u s) ∧ SpatialWeakGradient (u s) (G s) ∧
        EnergyStart ν u G s ∧ QFA.Assembly.Restart.RestartData ν u G s := Iff.rfl

example {ν R : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) (hR : 0 < R) :
    ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) R),
      Solenoidal (u s) ∧ SpatialWeakGradient (u s) (G s) ∧
        EnergyStart ν u G s ∧ QFA.Assembly.Restart.RestartData ν u G s :=
  LerayHopf.goodRestart_ae h hν hR

example {S ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hS : 0 < S) (hν : 0 < ν) (ha : a ≠ 0) :
    (safeCutoff S ‖a‖ ν / 2 ≤
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S ‖a‖ ν))).real
        {s | GoodRestart ν u G s ∧
          ‖u s‖ ^ 2 * (∑ j : Fin 3, ‖G s j‖ ^ 2) < productThreshold S ν}) ∧
      ∃ s, 0 < s ∧ s < safeCutoff S ‖a‖ ν ∧ GoodRestart ν u G s ∧
        ‖u s‖ ^ 2 * (∑ j : Fin 3, ‖G s j‖ ^ 2) < productThreshold S ν :=
  LerayHopf.safe_window_good_time_and_measure h hS hν ha

example {S ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hS : 0 < S) (hν : 0 < ν) (ha : a ≠ 0) :
    ∃ s, 0 < s ∧ s < safeCutoff S ‖a‖ ν ∧
      Solenoidal (u s) ∧ SpatialWeakGradient (u s) (G s) ∧
      EnergyStart ν u G s ∧ QFA.Assembly.Restart.RestartData ν u G s ∧
      Tendsto u (𝓝[>] s) (𝓝 (u s)) ∧
      ‖u s‖ ^ 2 * (∑ j : Fin 3, ‖G s j‖ ^ 2) < productThreshold S ν :=
  LerayHopf.exists_safe_restart h hS hν ha

end QFANativeFoundation.IntegrationTypeChecks

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.Space"
#check @MethbokeAddon.QuasiFeffermanA.Space
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.Space"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.Space"
#print axioms MethbokeAddon.QuasiFeffermanA.Space
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.Space"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SpatialL2"
#check @MethbokeAddon.QuasiFeffermanA.SpatialL2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SpatialL2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SpatialL2"
#print axioms MethbokeAddon.QuasiFeffermanA.SpatialL2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SpatialL2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.Velocity"
#check @MethbokeAddon.QuasiFeffermanA.Velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.Velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.Velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.Velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.Velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.WeakGradient"
#check @MethbokeAddon.QuasiFeffermanA.WeakGradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.WeakGradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.WeakGradient"
#print axioms MethbokeAddon.QuasiFeffermanA.WeakGradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.WeakGradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.coordinateVector"
#check @MethbokeAddon.QuasiFeffermanA.coordinateVector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.coordinateVector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.coordinateVector"
#print axioms MethbokeAddon.QuasiFeffermanA.coordinateVector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.coordinateVector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.scalarGradient"
#check @MethbokeAddon.QuasiFeffermanA.scalarGradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.scalarGradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.scalarGradient"
#print axioms MethbokeAddon.QuasiFeffermanA.scalarGradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.scalarGradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.Solenoidal"
#check @MethbokeAddon.QuasiFeffermanA.Solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.Solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.Solenoidal"
#print axioms MethbokeAddon.QuasiFeffermanA.Solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.Solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.EnergyDatum"
#check @MethbokeAddon.QuasiFeffermanA.EnergyDatum
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.EnergyDatum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.EnergyDatum"
#print axioms MethbokeAddon.QuasiFeffermanA.EnergyDatum
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.EnergyDatum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SpatialWeakGradient"
#check @MethbokeAddon.QuasiFeffermanA.SpatialWeakGradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SpatialWeakGradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SpatialWeakGradient"
#print axioms MethbokeAddon.QuasiFeffermanA.SpatialWeakGradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SpatialWeakGradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.MomentumTest"
#check @MethbokeAddon.QuasiFeffermanA.MomentumTest
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.MomentumTest"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.MomentumTest"
#print axioms MethbokeAddon.QuasiFeffermanA.MomentumTest
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.MomentumTest"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.momentumTimeIntegrand"
#check @MethbokeAddon.QuasiFeffermanA.momentumTimeIntegrand
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.momentumTimeIntegrand"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.momentumTimeIntegrand"
#print axioms MethbokeAddon.QuasiFeffermanA.momentumTimeIntegrand
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.momentumTimeIntegrand"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.momentumConvectionIntegrand"
#check @MethbokeAddon.QuasiFeffermanA.momentumConvectionIntegrand
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.momentumConvectionIntegrand"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.momentumConvectionIntegrand"
#print axioms MethbokeAddon.QuasiFeffermanA.momentumConvectionIntegrand
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.momentumConvectionIntegrand"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.momentumDissipationIntegrand"
#check @MethbokeAddon.QuasiFeffermanA.momentumDissipationIntegrand
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.momentumDissipationIntegrand"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.momentumDissipationIntegrand"
#print axioms MethbokeAddon.QuasiFeffermanA.momentumDissipationIntegrand
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.momentumDissipationIntegrand"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.WeakMomentum"
#check @MethbokeAddon.QuasiFeffermanA.WeakMomentum
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.WeakMomentum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.WeakMomentum"
#print axioms MethbokeAddon.QuasiFeffermanA.WeakMomentum
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.WeakMomentum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.EnergyStart"
#check @MethbokeAddon.QuasiFeffermanA.EnergyStart
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.EnergyStart"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.EnergyStart"
#print axioms MethbokeAddon.QuasiFeffermanA.EnergyStart
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.EnergyStart"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.energyStart_iff_qfa"
#check @MethbokeAddon.QuasiFeffermanA.energyStart_iff_qfa
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.energyStart_iff_qfa"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.energyStart_iff_qfa"
#print axioms MethbokeAddon.QuasiFeffermanA.energyStart_iff_qfa
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.energyStart_iff_qfa"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.energyProfile"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.energyProfile
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.energyProfile"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.energyProfile"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.energyProfile
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.energyProfile"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.initial_solenoidal"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.initial_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.initial_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.initial_solenoidal"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.initial_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.initial_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.velocity_energy_le_initial"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.velocity_energy_le_initial
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.velocity_energy_le_initial"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.velocity_energy_le_initial"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.velocity_energy_le_initial
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.velocity_energy_le_initial"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.energy_product_budget_Ioo"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.energy_product_budget_Ioo
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.energy_product_budget_Ioo"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.energy_product_budget_Ioo"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.energy_product_budget_Ioo
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.energy_product_budget_Ioo"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.energyStart_zero"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.energyStart_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.energyStart_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.energyStart_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.energyStart_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.energyStart_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.strong_right_trace"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.strong_right_trace
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.strong_right_trace"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.strong_right_trace"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.strong_right_trace
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.strong_right_trace"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.strong_initial_trace"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.strong_initial_trace
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.strong_initial_trace"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.strong_initial_trace"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.strong_initial_trace
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.strong_initial_trace"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.restart_energy_data"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.restart_energy_data
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.restart_energy_data"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.restart_energy_data"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.restart_energy_data
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.restart_energy_data"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.ae_restart_energy_data"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.ae_restart_energy_data
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.ae_restart_energy_data"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.ae_restart_energy_data"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.ae_restart_energy_data
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.ae_restart_energy_data"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.eq_zero_of_initial_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.eq_zero_of_initial_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.eq_zero_of_initial_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.eq_zero_of_initial_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.eq_zero_of_initial_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.eq_zero_of_initial_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.productThreshold"
#check @MethbokeAddon.QuasiFeffermanA.productThreshold
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.productThreshold"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.productThreshold"
#print axioms MethbokeAddon.QuasiFeffermanA.productThreshold
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.productThreshold"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.safeCutoff"
#check @MethbokeAddon.QuasiFeffermanA.safeCutoff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.safeCutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.safeCutoff"
#print axioms MethbokeAddon.QuasiFeffermanA.safeCutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.safeCutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.productThreshold_pos"
#check @MethbokeAddon.QuasiFeffermanA.productThreshold_pos
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.productThreshold_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.productThreshold_pos"
#print axioms MethbokeAddon.QuasiFeffermanA.productThreshold_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.productThreshold_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.safeCutoff_nonneg"
#check @MethbokeAddon.QuasiFeffermanA.safeCutoff_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.safeCutoff_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.safeCutoff_nonneg"
#print axioms MethbokeAddon.QuasiFeffermanA.safeCutoff_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.safeCutoff_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.safeCutoff_pos"
#check @MethbokeAddon.QuasiFeffermanA.safeCutoff_pos
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.safeCutoff_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.safeCutoff_pos"
#print axioms MethbokeAddon.QuasiFeffermanA.safeCutoff_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.safeCutoff_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.safeCutoff_zero"
#check @MethbokeAddon.QuasiFeffermanA.safeCutoff_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.safeCutoff_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.safeCutoff_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.safeCutoff_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.safeCutoff_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.threshold_mul_safeCutoff"
#check @MethbokeAddon.QuasiFeffermanA.threshold_mul_safeCutoff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.threshold_mul_safeCutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.threshold_mul_safeCutoff"
#print axioms MethbokeAddon.QuasiFeffermanA.threshold_mul_safeCutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.threshold_mul_safeCutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.budget_eq_half_threshold_cutoff"
#check @MethbokeAddon.QuasiFeffermanA.budget_eq_half_threshold_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.budget_eq_half_threshold_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.budget_eq_half_threshold_cutoff"
#print axioms MethbokeAddon.QuasiFeffermanA.budget_eq_half_threshold_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.budget_eq_half_threshold_cutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.budget_lt_threshold_cutoff"
#check @MethbokeAddon.QuasiFeffermanA.budget_lt_threshold_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.budget_lt_threshold_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.budget_lt_threshold_cutoff"
#print axioms MethbokeAddon.QuasiFeffermanA.budget_lt_threshold_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.budget_lt_threshold_cutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.safeCutoff_eq_pi_formula_of_sixth_power"
#check @MethbokeAddon.QuasiFeffermanA.safeCutoff_eq_pi_formula_of_sixth_power
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.safeCutoff_eq_pi_formula_of_sixth_power"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.safeCutoff_eq_pi_formula_of_sixth_power"
#print axioms MethbokeAddon.QuasiFeffermanA.safeCutoff_eq_pi_formula_of_sixth_power
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.safeCutoff_eq_pi_formula_of_sixth_power"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.exists_good_time_of_product_budget"
#check @MethbokeAddon.QuasiFeffermanA.exists_good_time_of_product_budget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.exists_good_time_of_product_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.exists_good_time_of_product_budget"
#print axioms MethbokeAddon.QuasiFeffermanA.exists_good_time_of_product_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.exists_good_time_of_product_budget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.exists_good_time_of_energy_envelope"
#check @MethbokeAddon.QuasiFeffermanA.exists_good_time_of_energy_envelope
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.exists_good_time_of_energy_envelope"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.exists_good_time_of_energy_envelope"
#print axioms MethbokeAddon.QuasiFeffermanA.exists_good_time_of_energy_envelope
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.exists_good_time_of_energy_envelope"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.subcritical_measure_ge_half"
#check @MethbokeAddon.QuasiFeffermanA.subcritical_measure_ge_half
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.subcritical_measure_ge_half"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.subcritical_measure_ge_half"
#print axioms MethbokeAddon.QuasiFeffermanA.subcritical_measure_ge_half
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.subcritical_measure_ge_half"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.good_set_measure_ge_half_of_product_budget"
#check @MethbokeAddon.QuasiFeffermanA.good_set_measure_ge_half_of_product_budget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.good_set_measure_ge_half_of_product_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.good_set_measure_ge_half_of_product_budget"
#print axioms MethbokeAddon.QuasiFeffermanA.good_set_measure_ge_half_of_product_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.good_set_measure_ge_half_of_product_budget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.good_time_and_measure_of_energy_envelope"
#check @MethbokeAddon.QuasiFeffermanA.good_time_and_measure_of_energy_envelope
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.good_time_and_measure_of_energy_envelope"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.good_time_and_measure_of_energy_envelope"
#print axioms MethbokeAddon.QuasiFeffermanA.good_time_and_measure_of_energy_envelope
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.good_time_and_measure_of_energy_envelope"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.GoodRestart"
#check @MethbokeAddon.QuasiFeffermanA.GoodRestart
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.GoodRestart"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.GoodRestart"
#print axioms MethbokeAddon.QuasiFeffermanA.GoodRestart
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.GoodRestart"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.goodRestart_ae"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.goodRestart_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.goodRestart_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.goodRestart_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.goodRestart_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.goodRestart_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.safe_window_good_time_and_measure"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.safe_window_good_time_and_measure
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.safe_window_good_time_and_measure"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.safe_window_good_time_and_measure"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.safe_window_good_time_and_measure
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.safe_window_good_time_and_measure"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_restart"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_restart
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_restart"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_restart"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_restart
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_restart"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.ae_eq_of_const_smul_real_multiplier_distribution"
#check @MethbokeAddon.QuasiFeffermanA.FourierMultipliers.ae_eq_of_const_smul_real_multiplier_distribution
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.ae_eq_of_const_smul_real_multiplier_distribution"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.ae_eq_of_const_smul_real_multiplier_distribution"
#print axioms MethbokeAddon.QuasiFeffermanA.FourierMultipliers.ae_eq_of_const_smul_real_multiplier_distribution
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.ae_eq_of_const_smul_real_multiplier_distribution"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.gradient_fourier_distribution_eq"
#check @MethbokeAddon.QuasiFeffermanA.FourierMultipliers.gradient_fourier_distribution_eq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.gradient_fourier_distribution_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.gradient_fourier_distribution_eq"
#print axioms MethbokeAddon.QuasiFeffermanA.FourierMultipliers.gradient_fourier_distribution_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.gradient_fourier_distribution_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.gradient_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.FourierMultipliers.gradient_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.gradient_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.gradient_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.FourierMultipliers.gradient_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.gradient_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.laplacian_fourier_distribution_eq"
#check @MethbokeAddon.QuasiFeffermanA.FourierMultipliers.laplacian_fourier_distribution_eq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.laplacian_fourier_distribution_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.laplacian_fourier_distribution_eq"
#print axioms MethbokeAddon.QuasiFeffermanA.FourierMultipliers.laplacian_fourier_distribution_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.laplacian_fourier_distribution_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.laplacian_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.FourierMultipliers.laplacian_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.laplacian_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.laplacian_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.FourierMultipliers.laplacian_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.FourierMultipliers.laplacian_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.fourierNormAEWitnesses_of_schwartzDerivativeWitnesses"
#check @MethbokeAddon.QuasiFeffermanA.fourierNormAEWitnesses_of_schwartzDerivativeWitnesses
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.fourierNormAEWitnesses_of_schwartzDerivativeWitnesses"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.fourierNormAEWitnesses_of_schwartzDerivativeWitnesses"
#print axioms MethbokeAddon.QuasiFeffermanA.fourierNormAEWitnesses_of_schwartzDerivativeWitnesses
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.fourierNormAEWitnesses_of_schwartzDerivativeWitnesses"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.nativeSpectralRealization_of_schwartzDerivativeWitnesses"
#check @MethbokeAddon.QuasiFeffermanA.nativeSpectralRealization_of_schwartzDerivativeWitnesses
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.nativeSpectralRealization_of_schwartzDerivativeWitnesses"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.nativeSpectralRealization_of_schwartzDerivativeWitnesses"
#print axioms MethbokeAddon.QuasiFeffermanA.nativeSpectralRealization_of_schwartzDerivativeWitnesses
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.nativeSpectralRealization_of_schwartzDerivativeWitnesses"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.wholeSpaceSpectralEndpoint"
#check @MethbokeAddon.QuasiFeffermanA.wholeSpaceSpectralEndpoint
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.wholeSpaceSpectralEndpoint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.wholeSpaceSpectralEndpoint"
#print axioms MethbokeAddon.QuasiFeffermanA.wholeSpaceSpectralEndpoint
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.wholeSpaceSpectralEndpoint"

