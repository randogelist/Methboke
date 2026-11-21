import QFAPhysicalStoppedGauge.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section
open Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform ENNReal

namespace QFAPhysicalStoppedGauge.ExpectedTypes
open MethbokeAddon.QuasiFeffermanA
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation

-- Literal native carriers, observation set and all budget/gauge definitions.
example : Space = EuclideanSpace ℝ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example (T : ℝ≥0∞) (τ : ℝ) : stoppedLifetime T τ = min T (ENNReal.ofReal τ) := rfl
example (T : ℝ≥0∞) (τ : ℝ) : stoppedEndpoint T τ = (min T (ENNReal.ofReal τ)).toReal := rfl
example (T : ℝ≥0∞) (τ : ℝ) : stoppedObservation T τ =
    {t : ℝ | 0 < t ∧ ENNReal.ofReal t < T ∧ t < τ} := rfl
example (u : PhysicalH1) : physicalFourierCharge u =
    ∫⁻ ξ : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (‖ξ‖ ^ 2 *
      ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) := rfl
example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalEnstrophyBudget U T τ =
      ∫⁻ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < T ∧ t < τ},
        ENNReal.ofReal ((physicalH1Enstrophy (U t)) ^ 2) := rfl
example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalSixBudget U T τ =
      ∫⁻ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < T ∧ t < τ},
        ENNReal.ofReal (∑ i : Fin 6, (physicalH1Enstrophy (physicalH1Sector i (U t))) ^ 2) := rfl
example (i : Fin 6) (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalSectorBudget i U T τ =
      ∫⁻ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < T ∧ t < τ},
        ENNReal.ofReal ((physicalH1Enstrophy (physicalH1Sector i (U t))) ^ 2) := rfl
example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalFourierBudget U T τ =
      ∫⁻ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < T ∧ t < τ},
        (∫⁻ ξ : Space, ENNReal.ofReal (‖ξ‖ ^ 2 *
          ‖(𝓕 (complexifyL2 (physicalH1Velocity (U t))) : ComplexL2) ξ‖ ^ 2)) ^ (2 : ℕ) := rfl
example (ν : ℝ) (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalStoppedGauge ν U T τ =
      (ENNReal.ofReal (4 * ν) * ∫⁻ t in {t : ℝ | 0 < t ∧ ENNReal.ofReal t < T ∧ t < τ},
        ENNReal.ofReal ((physicalH1Enstrophy (U t)) ^ 2)) ^ ((4 : ℝ)⁻¹) := rfl
example {ι : Type*} (ν : ℝ) (U : ι → ℝ → PhysicalH1)
    (T : ι → ℝ≥0∞) (τ : ι → ℝ) (R : ℝ) :
    physicalGaugeSublevel ν U T τ R =
      {a | physicalStoppedGauge ν (U a) (T a) (τ a) ≤ ENNReal.ofReal R} := rfl
example {ι : Type*} (ν : ℝ) (U : ι → ℝ → PhysicalH1)
    (T : ι → ℝ≥0∞) (τ : ι → ℝ) :
    physicalFiniteGaugeClass ν U T τ =
      {a | physicalStoppedGauge ν (U a) (T a) (τ a) ≠ (⊤ : ℝ≥0∞)} := rfl

-- Each public declaration is consumed at its complete independent type.
example (u : PhysicalH1) : ℝ≥0∞ :=
  @physicalFourierCharge u

example (u : PhysicalH1) :
    physicalFourierCharge u = ENNReal.ofReal (∫ ξ : Space, ‖ξ‖ ^ 2 *
      ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) :=
  @physicalFourierCharge_eq_ofReal u

example (u : PhysicalH1) :
    physicalFourierCharge u ≠ (⊤ : ℝ≥0∞) :=
  @physicalFourierCharge_finite u

example (u : PhysicalH1) :
    ENNReal.ofReal (physicalH1Enstrophy u) =
      ENNReal.ofReal (4 * Real.pi ^ 2) * physicalFourierCharge u :=
  @physicalEnstrophy_eq_fourierCharge u

example (u : PhysicalH1) :
    ENNReal.ofReal ((physicalH1Enstrophy u) ^ 2) =
      ENNReal.ofReal (16 * Real.pi ^ 4) * (physicalFourierCharge u) ^ 2 :=
  @physicalEnstrophy_sq_eq_fourierCharge_sq u

example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) : ℝ≥0∞ :=
  @physicalEnstrophyBudget U T τ

example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) : ℝ≥0∞ :=
  @physicalSixBudget U T τ

example (i : Fin 6) (U : ℝ → PhysicalH1)
    (T : ℝ≥0∞) (τ : ℝ) : ℝ≥0∞ :=
  @physicalSectorBudget i U T τ

example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) : ℝ≥0∞ :=
  @physicalFourierBudget U T τ

example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalEnstrophyBudget U T τ =
      ENNReal.ofReal (16 * Real.pi ^ 4) * physicalFourierBudget U T τ :=
  @physicalEnstrophyBudget_eq_fourierBudget U T τ

example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalEnstrophyBudget U T τ ≠ (⊤ : ℝ≥0∞) ↔
      physicalFourierBudget U T τ ≠ (⊤ : ℝ≥0∞) :=
  @physicalEnstrophyBudget_finite_iff_fourier U T τ

example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalSixBudget U T τ ≤ physicalEnstrophyBudget U T τ ∧
      physicalEnstrophyBudget U T τ ≤ 6 * physicalSixBudget U T τ :=
  @physicalStoppedBudget_bounds U T τ

example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalEnstrophyBudget U T τ ≠ (⊤ : ℝ≥0∞) ↔
      physicalSixBudget U T τ ≠ (⊤ : ℝ≥0∞) :=
  @physicalEnstrophyBudget_finite_iff_six U T τ

example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ)
    (hU : ContinuousOn U (stoppedObservation T τ)) :
    physicalSixBudget U T τ = ∑ i : Fin 6, physicalSectorBudget i U T τ :=
  @physicalSixBudget_eq_sum U T τ hU

example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ)
    (hU : ContinuousOn U (stoppedObservation T τ)) :
    physicalEnstrophyBudget U T τ ≠ (⊤ : ℝ≥0∞) ↔
      ∀ i : Fin 6, physicalSectorBudget i U T τ ≠ (⊤ : ℝ≥0∞) :=
  @physicalEnstrophyBudget_finite_iff_each U T τ hU

example (U : ℝ → PhysicalH1) (τ : ℝ) : physicalEnstrophyBudget U 0 τ = 0 :=
  @physicalEnstrophyBudget_zero_lifetime U τ

example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) : physicalEnstrophyBudget U T 0 = 0 :=
  @physicalEnstrophyBudget_zero_cutoff U T

example (T : ℝ≥0∞) (τ : ℝ) :
    physicalEnstrophyBudget (fun _ => 0) T τ = 0 :=
  @physicalEnstrophyBudget_zero T τ

example (U : ℝ → PhysicalH1) (τ : ℝ) : physicalSixBudget U 0 τ = 0 :=
  @physicalSixBudget_zero_lifetime U τ

example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) : physicalSixBudget U T 0 = 0 :=
  @physicalSixBudget_zero_cutoff U T

example (U : ℝ → PhysicalH1) (τ : ℝ) : physicalFourierBudget U 0 τ = 0 :=
  @physicalFourierBudget_zero_lifetime U τ

example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) : physicalFourierBudget U T 0 = 0 :=
  @physicalFourierBudget_zero_cutoff U T

example (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ)
    (hU : ContinuousOn U (Icc (0 : ℝ) (stoppedEndpoint T τ))) :
    physicalEnstrophyBudget U T τ ≠ (⊤ : ℝ≥0∞) :=
  @physicalEnstrophyBudget_finite_of_continuousOn U T τ hU

example (U : ℝ → PhysicalH1) {τ : ℝ} (hτ : 0 ≤ τ)
    (hU : ContinuousOn U (Icc (0 : ℝ) τ)) :
    physicalEnstrophyBudget U (⊤ : ℝ≥0∞) τ ≠ (⊤ : ℝ≥0∞) :=
  @physicalEnstrophyBudget_global_finite U τ hτ hU

example (ν : ℝ) (U : ℝ → PhysicalH1)
    (T : ℝ≥0∞) (τ : ℝ) : ℝ≥0∞ :=
  @physicalStoppedGauge ν U T τ

example (ν : ℝ) (U : ℝ → PhysicalH1)
    (T : ℝ≥0∞) (τ : ℝ) :
    physicalStoppedGauge ν U T τ ^ (4 : ℕ) =
      ENNReal.ofReal (4 * ν) * physicalEnstrophyBudget U T τ :=
  @physicalStoppedGauge_pow_four ν U T τ

example (ν : ℝ) (hν : 0 ≤ ν)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalStoppedGauge ν U T τ ^ (4 : ℕ) =
      ENNReal.ofReal (64 * Real.pi ^ 4 * ν) * physicalFourierBudget U T τ :=
  @physicalStoppedGauge_pow_four_fourier ν hν U T τ

example (ν : ℝ) (hν : 0 < ν)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalStoppedGauge ν U T τ ≠ (⊤ : ℝ≥0∞) ↔
      physicalEnstrophyBudget U T τ ≠ (⊤ : ℝ≥0∞) :=
  @physicalStoppedGauge_finite_iff ν hν U T τ

example (ν : ℝ) (hν : 0 < ν)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalStoppedGauge ν U T τ ≠ (⊤ : ℝ≥0∞) ↔
      physicalSixBudget U T τ ≠ (⊤ : ℝ≥0∞) :=
  @physicalStoppedGauge_finite_iff_six ν hν U T τ

example (ν : ℝ) (hν : 0 < ν)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalStoppedGauge ν U T τ ≠ (⊤ : ℝ≥0∞) ↔
      physicalFourierBudget U T τ ≠ (⊤ : ℝ≥0∞) :=
  @physicalStoppedGauge_finite_iff_fourier ν hν U T τ

example (ν : ℝ) (hν : 0 < ν)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ)
    (hU : ContinuousOn U (stoppedObservation T τ)) :
    physicalStoppedGauge ν U T τ ≠ (⊤ : ℝ≥0∞) ↔
      ∀ i : Fin 6, physicalSectorBudget i U T τ ≠ (⊤ : ℝ≥0∞) :=
  @physicalStoppedGauge_finite_iff_each ν hν U T τ hU

example (ν : ℝ)
    (U : ℝ → PhysicalH1) (τ : ℝ) : physicalStoppedGauge ν U 0 τ = 0 :=
  @physicalStoppedGauge_zero_lifetime ν U τ

example (ν : ℝ)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) : physicalStoppedGauge ν U T 0 = 0 :=
  @physicalStoppedGauge_zero_cutoff ν U T

example (ν : ℝ) (T : ℝ≥0∞) (τ : ℝ) :
    physicalStoppedGauge ν (fun _ => 0) T τ = 0 :=
  @physicalStoppedGauge_zero ν T τ

example (ν : ℝ) (hν : 0 < ν)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ R : ℝ) (hR : 0 ≤ R) :
    physicalStoppedGauge ν U T τ ≤ ENNReal.ofReal R ↔
      physicalEnstrophyBudget U T τ ≤ ENNReal.ofReal (R ^ 4 / (4 * ν)) :=
  @physicalStoppedGauge_le_iff ν hν U T τ R hR

example (ν : ℝ) (hν : 0 < ν)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ R : ℝ) (hR : 0 ≤ R) :
    physicalStoppedGauge ν U T τ ≤ ENNReal.ofReal R ↔
      physicalFourierBudget U T τ ≤
        ENNReal.ofReal (R ^ 4 / (64 * Real.pi ^ 4 * ν)) :=
  @physicalStoppedGauge_le_iff_fourier ν hν U T τ R hR

example {ι : Type*} (ν : ℝ) (U : ι → ℝ → PhysicalH1)
    (T : ι → ℝ≥0∞) (τ : ι → ℝ) (R : ℝ) : Set ι :=
  @physicalGaugeSublevel ι ν U T τ R

example {ι : Type*} (ν : ℝ) (U : ι → ℝ → PhysicalH1)
    (T : ι → ℝ≥0∞) (τ : ι → ℝ) : Set ι :=
  @physicalFiniteGaugeClass ι ν U T τ

example {ι : Type*} (ν : ℝ) (U : ι → ℝ → PhysicalH1)
    (T : ι → ℝ≥0∞) (τ : ι → ℝ) {R S : ℝ} (hRS : R ≤ S) :
    physicalGaugeSublevel ν U T τ R ⊆ physicalGaugeSublevel ν U T τ S :=
  @physicalGaugeSublevel_mono ι ν U T τ R S hRS

example {ι : Type*} (ν : ℝ)
    (U : ι → ℝ → PhysicalH1) (T : ι → ℝ≥0∞) (τ : ι → ℝ) (R : ℝ) :
    physicalGaugeSublevel ν U T τ R ⊆ physicalFiniteGaugeClass ν U T τ :=
  @physicalGaugeSublevel_subset_finite ι ν U T τ R

example {ι : Type*} (ν : ℝ)
    (U : ι → ℝ → PhysicalH1) (T : ι → ℝ≥0∞) (τ : ι → ℝ) :
    physicalFiniteGaugeClass ν U T τ =
      ⋃ n : ℕ, physicalGaugeSublevel ν U T τ (n : ℝ) :=
  @physicalFiniteGaugeClass_eq_iUnion ι ν U T τ

example {ι : Type*} (ν : ℝ) (hν : 0 < ν)
    (U : ι → ℝ → PhysicalH1) (T : ι → ℝ≥0∞) (τ : ι → ℝ) (a : ι) :
    a ∈ physicalFiniteGaugeClass ν U T τ ↔
      physicalSixBudget (U a) (T a) (τ a) ≠ (⊤ : ℝ≥0∞) :=
  @mem_physicalFiniteGaugeClass_iff_six ι ν hν U T τ a

end QFAPhysicalStoppedGauge.ExpectedTypes

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFourierCharge"
#check @MethbokeAddon.QuasiFeffermanA.physicalFourierCharge
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalFourierCharge"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFourierCharge"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalFourierCharge
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalFourierCharge"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFourierCharge_eq_ofReal"
#check @MethbokeAddon.QuasiFeffermanA.physicalFourierCharge_eq_ofReal
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalFourierCharge_eq_ofReal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFourierCharge_eq_ofReal"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalFourierCharge_eq_ofReal
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalFourierCharge_eq_ofReal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFourierCharge_finite"
#check @MethbokeAddon.QuasiFeffermanA.physicalFourierCharge_finite
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalFourierCharge_finite"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFourierCharge_finite"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalFourierCharge_finite
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalFourierCharge_finite"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophy_eq_fourierCharge"
#check @MethbokeAddon.QuasiFeffermanA.physicalEnstrophy_eq_fourierCharge
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophy_eq_fourierCharge"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophy_eq_fourierCharge"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalEnstrophy_eq_fourierCharge
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophy_eq_fourierCharge"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophy_sq_eq_fourierCharge_sq"
#check @MethbokeAddon.QuasiFeffermanA.physicalEnstrophy_sq_eq_fourierCharge_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophy_sq_eq_fourierCharge_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophy_sq_eq_fourierCharge_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalEnstrophy_sq_eq_fourierCharge_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophy_sq_eq_fourierCharge_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget"
#check @MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalSixBudget"
#check @MethbokeAddon.QuasiFeffermanA.physicalSixBudget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalSixBudget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalSixBudget"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalSixBudget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalSixBudget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalSectorBudget"
#check @MethbokeAddon.QuasiFeffermanA.physicalSectorBudget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalSectorBudget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalSectorBudget"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalSectorBudget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalSectorBudget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFourierBudget"
#check @MethbokeAddon.QuasiFeffermanA.physicalFourierBudget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalFourierBudget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFourierBudget"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalFourierBudget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalFourierBudget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_eq_fourierBudget"
#check @MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_eq_fourierBudget
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_eq_fourierBudget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_eq_fourierBudget"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_eq_fourierBudget
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_eq_fourierBudget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_fourier"
#check @MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_fourier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_fourier"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_fourier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedBudget_bounds"
#check @MethbokeAddon.QuasiFeffermanA.physicalStoppedBudget_bounds
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedBudget_bounds"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedBudget_bounds"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalStoppedBudget_bounds
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedBudget_bounds"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_six"
#check @MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_six
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_six"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_six"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_six
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_six"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalSixBudget_eq_sum"
#check @MethbokeAddon.QuasiFeffermanA.physicalSixBudget_eq_sum
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalSixBudget_eq_sum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalSixBudget_eq_sum"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalSixBudget_eq_sum
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalSixBudget_eq_sum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_each"
#check @MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_each
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_each"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_each"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_each
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_iff_each"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero_lifetime"
#check @MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero_lifetime
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero_lifetime"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero_lifetime"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero_lifetime
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero_lifetime"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero_cutoff"
#check @MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero_cutoff"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero_cutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero"
#check @MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalSixBudget_zero_lifetime"
#check @MethbokeAddon.QuasiFeffermanA.physicalSixBudget_zero_lifetime
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalSixBudget_zero_lifetime"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalSixBudget_zero_lifetime"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalSixBudget_zero_lifetime
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalSixBudget_zero_lifetime"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalSixBudget_zero_cutoff"
#check @MethbokeAddon.QuasiFeffermanA.physicalSixBudget_zero_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalSixBudget_zero_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalSixBudget_zero_cutoff"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalSixBudget_zero_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalSixBudget_zero_cutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFourierBudget_zero_lifetime"
#check @MethbokeAddon.QuasiFeffermanA.physicalFourierBudget_zero_lifetime
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalFourierBudget_zero_lifetime"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFourierBudget_zero_lifetime"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalFourierBudget_zero_lifetime
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalFourierBudget_zero_lifetime"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFourierBudget_zero_cutoff"
#check @MethbokeAddon.QuasiFeffermanA.physicalFourierBudget_zero_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalFourierBudget_zero_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFourierBudget_zero_cutoff"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalFourierBudget_zero_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalFourierBudget_zero_cutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_of_continuousOn"
#check @MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_of_continuousOn
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_of_continuousOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_of_continuousOn"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_of_continuousOn
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_finite_of_continuousOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_global_finite"
#check @MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_global_finite
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_global_finite"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_global_finite"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_global_finite
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalEnstrophyBudget_global_finite"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge"
#check @MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_pow_four"
#check @MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_pow_four
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_pow_four"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_pow_four"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_pow_four
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_pow_four"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_pow_four_fourier"
#check @MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_pow_four_fourier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_pow_four_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_pow_four_fourier"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_pow_four_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_pow_four_fourier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff"
#check @MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_six"
#check @MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_six
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_six"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_six"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_six
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_six"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_fourier"
#check @MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_fourier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_fourier"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_fourier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_each"
#check @MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_each
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_each"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_each"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_each
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_finite_iff_each"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero_lifetime"
#check @MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero_lifetime
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero_lifetime"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero_lifetime"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero_lifetime
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero_lifetime"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero_cutoff"
#check @MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero_cutoff"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero_cutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero"
#check @MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_le_iff"
#check @MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_le_iff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_le_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_le_iff"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_le_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_le_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_le_iff_fourier"
#check @MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_le_iff_fourier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_le_iff_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_le_iff_fourier"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_le_iff_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalStoppedGauge_le_iff_fourier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel"
#check @MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFiniteGaugeClass"
#check @MethbokeAddon.QuasiFeffermanA.physicalFiniteGaugeClass
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalFiniteGaugeClass"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFiniteGaugeClass"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalFiniteGaugeClass
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalFiniteGaugeClass"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel_mono"
#check @MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel_mono
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel_mono"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel_mono"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel_mono
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel_mono"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel_subset_finite"
#check @MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel_subset_finite
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel_subset_finite"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel_subset_finite"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel_subset_finite
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalGaugeSublevel_subset_finite"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFiniteGaugeClass_eq_iUnion"
#check @MethbokeAddon.QuasiFeffermanA.physicalFiniteGaugeClass_eq_iUnion
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalFiniteGaugeClass_eq_iUnion"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalFiniteGaugeClass_eq_iUnion"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalFiniteGaugeClass_eq_iUnion
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalFiniteGaugeClass_eq_iUnion"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.mem_physicalFiniteGaugeClass_iff_six"
#check @MethbokeAddon.QuasiFeffermanA.mem_physicalFiniteGaugeClass_iff_six
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.mem_physicalFiniteGaugeClass_iff_six"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.mem_physicalFiniteGaugeClass_iff_six"
#print axioms MethbokeAddon.QuasiFeffermanA.mem_physicalFiniteGaugeClass_iff_six
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.mem_physicalFiniteGaugeClass_iff_six"

