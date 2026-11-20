import MethbokeAddon.QuasiFeffermanA.FullStoppedBudget
import MethbokeAddon.QuasiFeffermanA.PhysicalH1Sectors
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Full physical stopped budgets and their fourth-root gauge

All quantities below use the actual native physical H1 graph and its constructed
six real Fourier projections. The time set is the open observation window
cut off by min(T, ofReal τ) before taking toReal. Every budget is an extended
nonnegative integral. None of the comparisons or gauge identities discards an
infinite value, assumes an endpoint extension, or supplies a solution theory.

The Fourier normalizations are literal: Y = 4*pi^2 F,
J = 16*pi^4 B and L^4 = 4*ν*J = 64*pi^4*ν*B.

Prepared source requires matching cached external compilation and named audits.
No local Lean, Lake or kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform ENNReal

namespace MethbokeAddon.QuasiFeffermanA

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation

/-- Literal full-volume weighted Fourier charge of the actual velocity. -/
def physicalFourierCharge (u : PhysicalH1) : ℝ≥0∞ :=
  ∫⁻ ξ : Space, ENNReal.ofReal (‖ξ‖ ^ 2 *
    ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2)

theorem physicalFourierCharge_eq_ofReal (u : PhysicalH1) :
    physicalFourierCharge u = ENNReal.ofReal (∫ ξ : Space, ‖ξ‖ ^ 2 *
      ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) :=
  H1Spectral.physicalH1_weighted_lintegral_eq u

theorem physicalFourierCharge_finite (u : PhysicalH1) :
    physicalFourierCharge u ≠ (⊤ : ℝ≥0∞) :=
  H1Spectral.physicalH1_weighted_lintegral_finite u

theorem physicalEnstrophy_eq_fourierCharge (u : PhysicalH1) :
    ENNReal.ofReal (physicalH1Enstrophy u) =
      ENNReal.ofReal (4 * Real.pi ^ 2) * physicalFourierCharge u := by
  rw [physicalFourierCharge_eq_ofReal, H1Spectral.physicalH1_enstrophy_eq_fourier,
    ENNReal.ofReal_mul (by positivity)]

theorem physicalEnstrophy_sq_eq_fourierCharge_sq (u : PhysicalH1) :
    ENNReal.ofReal ((physicalH1Enstrophy u) ^ 2) =
      ENNReal.ofReal (16 * Real.pi ^ 4) * (physicalFourierCharge u) ^ 2 := by
  rw [ENNReal.ofReal_pow (physicalH1Enstrophy_nonneg u),
    physicalEnstrophy_eq_fourierCharge, mul_pow,
    ← ENNReal.ofReal_pow (by positivity : 0 ≤ 4 * Real.pi ^ 2)]
  rw [show (4 * Real.pi ^ 2) ^ 2 = 16 * Real.pi ^ 4 by ring]

/-- Full physical enstrophy-square budget J; no finiteness is built in. -/
def physicalEnstrophyBudget (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) : ℝ≥0∞ :=
  fullStoppedBudget (fun t => ENNReal.ofReal ((physicalH1Enstrophy (U t)) ^ 2)) T τ

/-- Full sum-of-six physical charge-square budget J6. -/
def physicalSixBudget (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) : ℝ≥0∞ :=
  fullStoppedBudget
    (fun t => ENNReal.ofReal (∑ i : Fin 6, (physicalH1SectorCharge i (U t)) ^ 2)) T τ

/-- Each actual sector's full budget. -/
def physicalSectorBudget (i : Fin 6) (U : ℝ → PhysicalH1)
    (T : ℝ≥0∞) (τ : ℝ) : ℝ≥0∞ :=
  fullStoppedBudget (fun t => ENNReal.ofReal ((physicalH1SectorCharge i (U t)) ^ 2)) T τ

/-- Full time integral of the square of the literal weighted Fourier charge. -/
def physicalFourierBudget (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) : ℝ≥0∞ :=
  fullStoppedBudget (fun t => (physicalFourierCharge (U t)) ^ 2) T τ

theorem physicalEnstrophyBudget_eq_fourierBudget
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalEnstrophyBudget U T τ =
      ENNReal.ofReal (16 * Real.pi ^ 4) * physicalFourierBudget U T τ := by
  unfold physicalEnstrophyBudget physicalFourierBudget
  have h : (fun t => ENNReal.ofReal ((physicalH1Enstrophy (U t)) ^ 2)) =
      fun t => ENNReal.ofReal (16 * Real.pi ^ 4) * (physicalFourierCharge (U t)) ^ 2 :=
    funext fun t => physicalEnstrophy_sq_eq_fourierCharge_sq (U t)
  rw [h]
  exact fullStoppedBudget_const_mul _ _ T τ ENNReal.ofReal_ne_top

theorem physicalEnstrophyBudget_finite_iff_fourier
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalEnstrophyBudget U T τ ≠ (⊤ : ℝ≥0∞) ↔
      physicalFourierBudget U T τ ≠ (⊤ : ℝ≥0∞) := by
  rw [physicalEnstrophyBudget_eq_fourierBudget]
  constructor
  · intro h
    exact (ENNReal.lt_top_of_mul_ne_top_right h (by positivity)).ne
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top

/-- The factor-six comparison holds on the whole stopped window, including∞. -/
theorem physicalStoppedBudget_bounds (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalSixBudget U T τ ≤ physicalEnstrophyBudget U T τ ∧
      physicalEnstrophyBudget U T τ ≤ 6 * physicalSixBudget U T τ := by
  simpa only [physicalSixBudget, physicalEnstrophyBudget, fullStoppedBudget,
    stoppedObservation_eq_Ioo, sixChargeBudget, stoppedSquareBudget] using
    physicalH1Sector_budget_bounds U (stoppedEndpoint T τ)

theorem physicalEnstrophyBudget_finite_iff_six
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalEnstrophyBudget U T τ ≠ (⊤ : ℝ≥0∞) ↔
      physicalSixBudget U T τ ≠ (⊤ : ℝ≥0∞) := by
  simpa only [physicalSixBudget, physicalEnstrophyBudget, fullStoppedBudget,
    stoppedObservation_eq_Ioo, sixChargeBudget, stoppedSquareBudget] using
    physicalH1Sector_budget_finite_iff U (stoppedEndpoint T τ)

theorem physicalSixBudget_eq_sum (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ)
    (hU : ContinuousOn U (stoppedObservation T τ)) :
    physicalSixBudget U T τ = ∑ i : Fin 6, physicalSectorBudget i U T τ := by
  rw [stoppedObservation_eq_Ioo] at hU
  simpa only [physicalSixBudget, physicalSectorBudget, fullStoppedBudget,
    stoppedObservation_eq_Ioo, sixChargeBudget] using
    physicalH1Sector_budget_eq_sum U (stoppedEndpoint T τ) hU

theorem physicalEnstrophyBudget_finite_iff_each
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ)
    (hU : ContinuousOn U (stoppedObservation T τ)) :
    physicalEnstrophyBudget U T τ ≠ (⊤ : ℝ≥0∞) ↔
      ∀ i : Fin 6, physicalSectorBudget i U T τ ≠ (⊤ : ℝ≥0∞) := by
  rw [physicalEnstrophyBudget_finite_iff_six, physicalSixBudget_eq_sum U T τ hU]
  simp only [ENNReal.sum_ne_top, Finset.mem_univ, true_implies]

@[simp] theorem physicalEnstrophyBudget_zero_lifetime
    (U : ℝ → PhysicalH1) (τ : ℝ) : physicalEnstrophyBudget U 0 τ = 0 := by
  exact fullStoppedBudget_zero_lifetime _ τ

@[simp] theorem physicalEnstrophyBudget_zero_cutoff
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) : physicalEnstrophyBudget U T 0 = 0 := by
  exact fullStoppedBudget_zero_cutoff _ T

@[simp] theorem physicalEnstrophyBudget_zero (T : ℝ≥0∞) (τ : ℝ) :
    physicalEnstrophyBudget (fun _ => 0) T τ = 0 := by
  simp [physicalEnstrophyBudget, physicalH1Enstrophy, fullStoppedBudget]

@[simp] theorem physicalSixBudget_zero_lifetime
    (U : ℝ → PhysicalH1) (τ : ℝ) : physicalSixBudget U 0 τ = 0 :=
  fullStoppedBudget_zero_lifetime _ τ

@[simp] theorem physicalSixBudget_zero_cutoff
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) : physicalSixBudget U T 0 = 0 :=
  fullStoppedBudget_zero_cutoff _ T

@[simp] theorem physicalFourierBudget_zero_lifetime
    (U : ℝ → PhysicalH1) (τ : ℝ) : physicalFourierBudget U 0 τ = 0 :=
  fullStoppedBudget_zero_lifetime _ τ

@[simp] theorem physicalFourierBudget_zero_cutoff
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) : physicalFourierBudget U T 0 = 0 :=
  fullStoppedBudget_zero_cutoff _ T

/-- At a genuinely available full closed slab, compact continuity gives the
whole budget's finiteness. The continuity premise is retained explicitly. -/
theorem physicalEnstrophyBudget_finite_of_continuousOn
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ)
    (hU : ContinuousOn U (Icc (0 : ℝ) (stoppedEndpoint T τ))) :
    physicalEnstrophyBudget U T τ ≠ (⊤ : ℝ≥0∞) := by
  simpa only [physicalEnstrophyBudget, fullStoppedBudget,
    stoppedObservation_eq_Ioo, stoppedSquareBudget] using
    physicalH1_stoppedSquareBudget_finite U hU

theorem physicalEnstrophyBudget_global_finite
    (U : ℝ → PhysicalH1) {τ : ℝ} (hτ : 0 ≤ τ)
    (hU : ContinuousOn U (Icc (0 : ℝ) τ)) :
    physicalEnstrophyBudget U (⊤ : ℝ≥0∞) τ ≠ (⊤ : ℝ≥0∞) := by
  apply physicalEnstrophyBudget_finite_of_continuousOn
  simpa only [stoppedEndpoint_top hτ] using hU

/-- The full extended fourth-root gauge. A positive viscosity is required
for its finiteness to characterize budget finiteness. -/
def physicalStoppedGauge (ν : ℝ) (U : ℝ → PhysicalH1)
    (T : ℝ≥0∞) (τ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (4 * ν) * physicalEnstrophyBudget U T τ) ^ ((4 : ℝ)⁻¹)

theorem physicalStoppedGauge_pow_four (ν : ℝ) (U : ℝ → PhysicalH1)
    (T : ℝ≥0∞) (τ : ℝ) :
    physicalStoppedGauge ν U T τ ^ (4 : ℕ) =
      ENNReal.ofReal (4 * ν) * physicalEnstrophyBudget U T τ := by
  exact ENNReal.rpow_inv_natCast_pow (by decide : (4 : ℕ) ≠ 0) _

theorem physicalStoppedGauge_pow_four_fourier (ν : ℝ) (hν : 0 ≤ ν)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalStoppedGauge ν U T τ ^ (4 : ℕ) =
      ENNReal.ofReal (64 * Real.pi ^ 4 * ν) * physicalFourierBudget U T τ := by
  rw [physicalStoppedGauge_pow_four, physicalEnstrophyBudget_eq_fourierBudget,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * ν)]
  rw [show (4 * ν) * (16 * Real.pi ^ 4) = 64 * Real.pi ^ 4 * ν by ring]

theorem physicalStoppedGauge_finite_iff (ν : ℝ) (hν : 0 < ν)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalStoppedGauge ν U T τ ≠ (⊤ : ℝ≥0∞) ↔
      physicalEnstrophyBudget U T τ ≠ (⊤ : ℝ≥0∞) := by
  unfold physicalStoppedGauge
  rw [Ne, ENNReal.rpow_eq_top_iff_of_pos (by positivity)]
  constructor
  · intro h
    exact (ENNReal.lt_top_of_mul_ne_top_right h (by positivity)).ne
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top

theorem physicalStoppedGauge_finite_iff_six (ν : ℝ) (hν : 0 < ν)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalStoppedGauge ν U T τ ≠ (⊤ : ℝ≥0∞) ↔
      physicalSixBudget U T τ ≠ (⊤ : ℝ≥0∞) :=
  (physicalStoppedGauge_finite_iff ν hν U T τ).trans
    (physicalEnstrophyBudget_finite_iff_six U T τ)

theorem physicalStoppedGauge_finite_iff_fourier (ν : ℝ) (hν : 0 < ν)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ) :
    physicalStoppedGauge ν U T τ ≠ (⊤ : ℝ≥0∞) ↔
      physicalFourierBudget U T τ ≠ (⊤ : ℝ≥0∞) :=
  (physicalStoppedGauge_finite_iff ν hν U T τ).trans
    (physicalEnstrophyBudget_finite_iff_fourier U T τ)

theorem physicalStoppedGauge_finite_iff_each (ν : ℝ) (hν : 0 < ν)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ : ℝ)
    (hU : ContinuousOn U (stoppedObservation T τ)) :
    physicalStoppedGauge ν U T τ ≠ (⊤ : ℝ≥0∞) ↔
      ∀ i : Fin 6, physicalSectorBudget i U T τ ≠ (⊤ : ℝ≥0∞) :=
  (physicalStoppedGauge_finite_iff ν hν U T τ).trans
    (physicalEnstrophyBudget_finite_iff_each U T τ hU)

@[simp] theorem physicalStoppedGauge_zero_lifetime (ν : ℝ)
    (U : ℝ → PhysicalH1) (τ : ℝ) : physicalStoppedGauge ν U 0 τ = 0 := by
  simp [physicalStoppedGauge, ENNReal.zero_rpow_of_pos (by positivity : 0 < (4 : ℝ)⁻¹)]

@[simp] theorem physicalStoppedGauge_zero_cutoff (ν : ℝ)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) : physicalStoppedGauge ν U T 0 = 0 := by
  simp [physicalStoppedGauge, ENNReal.zero_rpow_of_pos (by positivity : 0 < (4 : ℝ)⁻¹)]

@[simp] theorem physicalStoppedGauge_zero (ν : ℝ) (T : ℝ≥0∞) (τ : ℝ) :
    physicalStoppedGauge ν (fun _ => 0) T τ = 0 := by
  simp [physicalStoppedGauge, ENNReal.zero_rpow_of_pos (by positivity : 0 < (4 : ℝ)⁻¹)]

/-- Exact finite-radius bound, still an extended-real statement on the left. -/
theorem physicalStoppedGauge_le_iff (ν : ℝ) (hν : 0 < ν)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ R : ℝ) (hR : 0 ≤ R) :
    physicalStoppedGauge ν U T τ ≤ ENNReal.ofReal R ↔
      physicalEnstrophyBudget U T τ ≤ ENNReal.ofReal (R ^ 4 / (4 * ν)) := by
  have h4ν : 0 < 4 * ν := by positivity
  have hc : ENNReal.ofReal (4 * ν) ≠ 0 := by positivity
  rw [physicalStoppedGauge, ENNReal.rpow_inv_le_iff (by norm_num : 0 < (4 : ℝ)),
    show (ENNReal.ofReal R) ^ (4 : ℝ) = (ENNReal.ofReal R) ^ (4 : ℕ) from
      ENNReal.rpow_natCast _ 4,
    ← ENNReal.ofReal_pow hR,
    ENNReal.ofReal_div_of_pos h4ν,
    ENNReal.le_div_iff_mul_le (Or.inl hc) (Or.inl ENNReal.ofReal_ne_top)]
  rw [mul_comm]

theorem physicalStoppedGauge_le_iff_fourier (ν : ℝ) (hν : 0 < ν)
    (U : ℝ → PhysicalH1) (T : ℝ≥0∞) (τ R : ℝ) (hR : 0 ≤ R) :
    physicalStoppedGauge ν U T τ ≤ ENNReal.ofReal R ↔
      physicalFourierBudget U T τ ≤
        ENNReal.ofReal (R ^ 4 / (64 * Real.pi ^ 4 * ν)) := by
  have hc : 0 < 64 * Real.pi ^ 4 * ν := by positivity
  have hp : physicalStoppedGauge ν U T τ ≤ ENNReal.ofReal R ↔
      physicalStoppedGauge ν U T τ ^ (4 : ℕ) ≤ (ENNReal.ofReal R) ^ (4 : ℕ) := by
    simpa only [ENNReal.rpow_ofNat] using
      (ENNReal.rpow_le_rpow_iff (x := physicalStoppedGauge ν U T τ)
        (y := ENNReal.ofReal R) (by norm_num : 0 < (4 : ℝ))).symm
  rw [hp, physicalStoppedGauge_pow_four_fourier ν hν.le,
    ← ENNReal.ofReal_pow hR, ENNReal.ofReal_div_of_pos hc,
    ENNReal.le_div_iff_mul_le (Or.inl (by positivity :
      ENNReal.ofReal (64 * Real.pi ^ 4 * ν) ≠ 0)) (Or.inl ENNReal.ofReal_ne_top)]
  rw [mul_comm]

/-- Finite-radius sublevels for any supplied indexed family of actual paths.
This definition does not assert that a canonical solution family exists. -/
def physicalGaugeSublevel {ι : Type*} (ν : ℝ) (U : ι → ℝ → PhysicalH1)
    (T : ι → ℝ≥0∞) (τ : ι → ℝ) (R : ℝ) : Set ι :=
  {a | physicalStoppedGauge ν (U a) (T a) (τ a) ≤ ENNReal.ofReal R}

/-- Finite full gauge class; no global-lifetime property enters the definition. -/
def physicalFiniteGaugeClass {ι : Type*} (ν : ℝ) (U : ι → ℝ → PhysicalH1)
    (T : ι → ℝ≥0∞) (τ : ι → ℝ) : Set ι :=
  {a | physicalStoppedGauge ν (U a) (T a) (τ a) ≠ (⊤ : ℝ≥0∞)}

theorem physicalGaugeSublevel_mono {ι : Type*} (ν : ℝ) (U : ι → ℝ → PhysicalH1)
    (T : ι → ℝ≥0∞) (τ : ι → ℝ) {R S : ℝ} (hRS : R ≤ S) :
    physicalGaugeSublevel ν U T τ R ⊆ physicalGaugeSublevel ν U T τ S :=
  fun _ ha => ha.trans (ENNReal.ofReal_le_ofReal hRS)

theorem physicalGaugeSublevel_subset_finite {ι : Type*} (ν : ℝ)
    (U : ι → ℝ → PhysicalH1) (T : ι → ℝ≥0∞) (τ : ι → ℝ) (R : ℝ) :
    physicalGaugeSublevel ν U T τ R ⊆ physicalFiniteGaugeClass ν U T τ :=
  fun _ ha => ne_top_of_le_ne_top ENNReal.ofReal_ne_top ha

/-- The finite full gauge class is exactly exhausted by integer sublevels. -/
theorem physicalFiniteGaugeClass_eq_iUnion {ι : Type*} (ν : ℝ)
    (U : ι → ℝ → PhysicalH1) (T : ι → ℝ≥0∞) (τ : ι → ℝ) :
    physicalFiniteGaugeClass ν U T τ =
      ⋃ n : ℕ, physicalGaugeSublevel ν U T τ (n : ℝ) := by
  ext a
  constructor
  · intro ha
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change physicalStoppedGauge ν (U a) (T a) (τ a) ≤ ENNReal.ofReal (n : ℝ)
    simpa only [ENNReal.ofReal_natCast] using hn.le
  · intro ha
    obtain ⟨n, hn⟩ := mem_iUnion.mp ha
    exact physicalGaugeSublevel_subset_finite ν U T τ (n : ℝ) hn

theorem mem_physicalFiniteGaugeClass_iff_six {ι : Type*} (ν : ℝ) (hν : 0 < ν)
    (U : ι → ℝ → PhysicalH1) (T : ι → ℝ≥0∞) (τ : ι → ℝ) (a : ι) :
    a ∈ physicalFiniteGaugeClass ν U T τ ↔
      physicalSixBudget (U a) (T a) (τ a) ≠ (⊤ : ℝ≥0∞) :=
  physicalStoppedGauge_finite_iff_six ν hν (U a) (T a) (τ a)

end MethbokeAddon.QuasiFeffermanA
