import MethbokeAddon.WeakFouriermanB.FourierBudget
import MethbokeAddon.WeakFouriermanB.LocalFront

/-!
Homogeneous physical Fourier-budget adapter for Weak_Fourierman_B.

The pinned homogeneous L6 proof is localized to arbitrary smooth, periodic,
mean-zero fields. The actual physical H1 Fourier datum supplies Parseval and
the order-lowering contraction supplies E <= D. No solution wrapper, PDE,
initial energy, energy trace, or assumed energy bound is used.

The final theorem gives the actual spatial L6 norm in time L4 on the SAME
open front. It does not establish continuation or global regularity.
The extended full-mode Fourier sum retains infinity. Prepared source only;
external verification is required, and no local Lean execution was performed.
-/

set_option autoImplicit false

open Set MeasureTheory Filter SingularClosure
open scoped BigOperators ENNReal ContDiff Topology

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- Physical mean zero implies zero actual Fourier mode without a
divergence-free or solution hypothesis. -/
theorem meanZero_datumFourierCoeff_meanZero
    (v : Field) (hz : MeanZero v) :
    SpectralMeanZero (datumFourierCoeff v) := by
  intro i
  rw [datumFourierCoeff_zero hz.1, hz.2]
  simp

/-- Poincare in the coarse normalization needed below, for an actual field.
Both norms are identified with the same actual Fourier coefficients. -/
theorem smooth_periodic_meanZero_energy_le_dissipation
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (hz : MeanZero v) :
    physicalEnergy v ≤ physicalDissipation v := by
  have hH1 := physicalH1_of_smooth_periodic v hv hp
  have hzero := meanZero_datumFourierCoeff_meanZero v hz
  let w : CriticalSobolev 2 := QuasiFeffermanB.physicalH1SobolevDatum hH1 hzero
  have hw : criticalCoeff 2 w = datumFourierCoeff v :=
    QuasiFeffermanB.physicalH1SobolevDatum_coeff hH1 hzero
  let w0 : CriticalSobolev 0 := criticalSobolevLower 0 2 (by norm_num) w
  have hw0 : criticalCoeff 0 w0 = datumFourierCoeff v := by
    rw [criticalSobolevLower_coeff, hw]
  have hrapid := ALL_SOBOLEV_IMP_RAPID_SCALAR (datumFourierCoeff v)
    (fun s => SMOOTH_DATUM_MEM_TORUS_SOBOLEV s v hv hp)
  have hE := critical_smoothFourierSynthesis_energy_eq_norm_sq
    (datumFourierCoeff v) hrapid (datumFourierCoeff_reality v) w0 hw0
  have hD := critical_smoothFourierSynthesis_dissipation_eq_norm_sq
    (datumFourierCoeff v) hrapid (datumFourierCoeff_reality v) hzero w hw
  rw [smoothFourierSynthesis_datum_eq v hv hp] at hE hD
  rw [hE, hD]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (criticalSobolevLower_norm_le 0 2 (by norm_num) w) 2

/-- The spatial L6 fourth power is controlled solely by squared dissipation.
The constant is independent of the field and of any time interval. -/
theorem SMOOTH_MEAN_ZERO_HOMOGENEOUS_L6_FOURTH :
    ∃ K : ℝ, 0 < K ∧ ∀ v : Field, ContDiff ℝ ∞ v → SpatialPeriodic v →
      MeanZero v → criticalSpatialNorm 6 v ^ 4 ≤ K * physicalDissipation v ^ 2 := by
  obtain ⟨K, hK, hb⟩ := CRITICAL_SMOOTH_L6_FOURTH_BOUND
  refine ⟨10 * K, by positivity, ?_⟩
  intro v hv hp hz
  have hE := smooth_periodic_meanZero_energy_le_dissipation v hv hp hz
  have hE0 : 0 ≤ physicalEnergy v := by
    rw [physicalEnergy_eq_integral_norm_sq]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hE2 := pow_le_pow_left₀ hE0 hE 2
  calc
    _ ≤ K * (9 * physicalDissipation v ^ 2 + physicalEnergy v ^ 2) := hb v hv hp
    _ ≤ K * (9 * physicalDissipation v ^ 2 + physicalDissipation v ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hE2) hK.le
    _ = _ := by ring

def homogeneousL6FourthConstant : ℝ :=
  SMOOTH_MEAN_ZERO_HOMOGENEOUS_L6_FOURTH.choose

theorem homogeneousL6FourthConstant_pos : 0 < homogeneousL6FourthConstant :=
  SMOOTH_MEAN_ZERO_HOMOGENEOUS_L6_FOURTH.choose_spec.1

theorem homogeneousL6FourthConstant_bound
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (hz : MeanZero v) :
    criticalSpatialNorm 6 v ^ 4 ≤ homogeneousL6FourthConstant * physicalDissipation v ^ 2 :=
  SMOOTH_MEAN_ZERO_HOMOGENEOUS_L6_FOURTH.choose_spec.2 v hv hp hz

/-- Homogeneous domination works for an arbitrary time measure; no finite
time-measure or kinetic-energy integrability premise is necessary. -/
theorem homogeneous_l6_fourth_integrable_of_dissipation_square
    (μ : Measure ℝ) (u : ℝ → Field)
    (hregular : ∀ᵐ t ∂μ,
      ContDiff ℝ ∞ (u t) ∧ SpatialPeriodic (u t) ∧ MeanZero (u t))
    (hmeas : AEStronglyMeasurable (fun t => criticalSpatialNorm 6 (u t)) μ)
    (hD : Integrable (fun t => physicalDissipation (u t) ^ 2) μ) :
    Integrable (fun t => criticalSpatialNorm 6 (u t) ^ 4) μ := by
  apply (hD.const_mul homogeneousL6FourthConstant).mono' (hmeas.pow 4)
  filter_upwards [hregular] with t ht
  change ‖criticalSpatialNorm 6 (u t) ^ 4‖ ≤
    homogeneousL6FourthConstant * physicalDissipation (u t) ^ 2
  rw [Real.norm_of_nonneg (pow_nonneg (criticalSpatialNorm_nonneg 6 _) 4)]
  exact homogeneousL6FourthConstant_bound (u t) ht.1 ht.2.1 ht.2.2

theorem homogeneous_serrin_of_dissipation_square
    (μ : Measure ℝ) (u : ℝ → Field)
    (hregular : ∀ᵐ t ∂μ,
      ContDiff ℝ ∞ (u t) ∧ SpatialPeriodic (u t) ∧ MeanZero (u t))
    (hmeas : AEStronglyMeasurable (fun t => criticalSpatialNorm 6 (u t)) μ)
    (hD : Integrable (fun t => physicalDissipation (u t) ^ 2) μ) :
    MemLp (fun t => criticalSpatialNorm 6 (u t)) 4 μ := by
  have hfour := homogeneous_l6_fourth_integrable_of_dissipation_square
    μ u hregular hmeas hD
  apply (integrable_norm_rpow_iff hmeas
    (by norm_num : (4 : ℝ≥0∞) ≠ 0)
    (by norm_num : (4 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))).mp
  have hnorm (t : ℝ) : ‖criticalSpatialNorm 6 (u t)‖ = criticalSpatialNorm 6 (u t) :=
    Real.norm_of_nonneg (criticalSpatialNorm_nonneg 6 _)
  have hpow (x : ℝ) : x ^ (4 : ℝ) = x ^ (4 : ℕ) := Real.rpow_ofNat x 4
  simpa only [ENNReal.toReal_ofNat, hnorm, hpow] using hfour

/-- The full Fourier budget gives squared physical dissipation integrability
for these exact slices. Summability and Parseval are proved from the physical
fields, rather than required as separate spectral assumptions. -/
theorem homogeneous_dissipation_square_integrable_of_fourier_budget
    (μ : Measure ℝ) (u : ℝ → Field)
    (hregular : ∀ᵐ t ∂μ,
      ContDiff ℝ ∞ (u t) ∧ SpatialPeriodic (u t) ∧ MeanZero (u t))
    (hDmeas : AEStronglyMeasurable (fun t => physicalDissipation (u t)) μ)
    (hbudget : (∫⁻ t, ExtendedFourierEnstrophy (datumFourierCoeff (u t)) ^ 2 ∂μ) <
      (⊤ : ℝ≥0∞)) :
    Integrable (fun t => physicalDissipation (u t) ^ 2) μ := by
  have hdata (t : ℝ)
      (ht : ContDiff ℝ ∞ (u t) ∧ SpatialPeriodic (u t) ∧ MeanZero (u t)) :
      physicalDissipation (u t) =
        (4 * Real.pi ^ 2) * FourierEnstrophy (datumFourierCoeff (u t)) ∧
      ENNReal.ofReal (FourierEnstrophy (datumFourierCoeff (u t))) =
        ExtendedFourierEnstrophy (datumFourierCoeff (u t)) := by
    have hH1 := physicalH1_of_smooth_periodic (u t) ht.1 ht.2.1
    have hzero := meanZero_datumFourierCoeff_meanZero (u t) ht.2.2
    let w : CriticalSobolev 2 := QuasiFeffermanB.physicalH1SobolevDatum hH1 hzero
    have hw : criticalCoeff 2 w = datumFourierCoeff (u t) :=
      QuasiFeffermanB.physicalH1SobolevDatum_coeff hH1 hzero
    constructor
    · have hrapid := ALL_SOBOLEV_IMP_RAPID_SCALAR (datumFourierCoeff (u t))
        (fun s => SMOOTH_DATUM_MEM_TORUS_SOBOLEV s (u t) ht.1 ht.2.1)
      have hD := smoothSynthesis_dissipation_eq_fourierEnstrophy
        (datumFourierCoeff (u t)) hrapid (datumFourierCoeff_reality (u t)) hzero w hw
      simpa only [smoothFourierSynthesis_datum_eq (u t) ht.1 ht.2.1] using hD
    · exact ofReal_fourierEnstrophy_eq_extended (datumFourierCoeff (u t))
        (fourierEnstrophy_summable (datumFourierCoeff (u t)) hzero w hw)
  exact dissipation_square_integrable_of_fourier_budget μ u
    (fun t => datumFourierCoeff (u t)) hDmeas
    (hregular.mono fun t ht => (hdata t ht).1)
    (hregular.mono fun t ht => (hdata t ht).2) hbudget

/-- Actual full Fourier budget to actual physical Serrin norm, without an
energy bound, an initial trace, or a global solution wrapper. -/
theorem homogeneous_physical_fourier_budget_to_serrin
    (μ : Measure ℝ) (u : ℝ → Field)
    (hregular : ∀ᵐ t ∂μ,
      ContDiff ℝ ∞ (u t) ∧ SpatialPeriodic (u t) ∧ MeanZero (u t))
    (hL6meas : AEStronglyMeasurable (fun t => criticalSpatialNorm 6 (u t)) μ)
    (hDmeas : AEStronglyMeasurable (fun t => physicalDissipation (u t)) μ)
    (hbudget : (∫⁻ t, ExtendedFourierEnstrophy (datumFourierCoeff (u t)) ^ 2 ∂μ) <
      (⊤ : ℝ≥0∞)) :
    MemLp (fun t => criticalSpatialNorm 6 (u t)) 4 μ :=
  homogeneous_serrin_of_dissipation_square μ u hregular hL6meas
    (homogeneous_dissipation_square_integrable_of_fourier_budget
      μ u hregular hDmeas hbudget)

/-- Local joint smoothness supplies all time measurability and slice
smoothness. Only periodicity, physical mean zero and the full Fourier budget
are additionally required on the same open front. -/
theorem local_homogeneous_fourier_budget_to_serrin
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (hp : ∀ t ∈ Ioo (0 : ℝ) T, SpatialPeriodic (u t))
    (hz : ∀ t ∈ Ioo (0 : ℝ) T, MeanZero (u t))
    (hbudget : FourierBudgetFinite (fun t => datumFourierCoeff (u t)) T) :
    MemLp (fun t => criticalSpatialNorm 6 (u t)) 4
      (volume.restrict (Ioo (0 : ℝ) T)) := by
  have hmem : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), t ∈ Ioo (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Ioo
  exact homogeneous_physical_fourier_budget_to_serrin
    (volume.restrict (Ioo (0 : ℝ) T)) u
    (hmem.mono fun t ht =>
      ⟨local_spatial_slice_contDiff u T hu t ht, hp t ht, hz t ht⟩)
    (local_spatialNorm_six_aestronglyMeasurable u T hu.continuousOn)
    (local_physicalDissipation_aestronglyMeasurable u T hu) hbudget

end
end MethbokeAddon.WeakFouriermanB

set_option pp.fullNames true

#check MethbokeAddon.WeakFouriermanB.meanZero_datumFourierCoeff_meanZero
#print axioms MethbokeAddon.WeakFouriermanB.meanZero_datumFourierCoeff_meanZero
#check MethbokeAddon.WeakFouriermanB.smooth_periodic_meanZero_energy_le_dissipation
#print axioms MethbokeAddon.WeakFouriermanB.smooth_periodic_meanZero_energy_le_dissipation
#check MethbokeAddon.WeakFouriermanB.SMOOTH_MEAN_ZERO_HOMOGENEOUS_L6_FOURTH
#print axioms MethbokeAddon.WeakFouriermanB.SMOOTH_MEAN_ZERO_HOMOGENEOUS_L6_FOURTH
#check MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_pos
#print axioms MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_pos
#check MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_bound
#print axioms MethbokeAddon.WeakFouriermanB.homogeneousL6FourthConstant_bound
#check MethbokeAddon.WeakFouriermanB.homogeneous_l6_fourth_integrable_of_dissipation_square
#print axioms MethbokeAddon.WeakFouriermanB.homogeneous_l6_fourth_integrable_of_dissipation_square
#check MethbokeAddon.WeakFouriermanB.homogeneous_serrin_of_dissipation_square
#print axioms MethbokeAddon.WeakFouriermanB.homogeneous_serrin_of_dissipation_square
#check MethbokeAddon.WeakFouriermanB.homogeneous_dissipation_square_integrable_of_fourier_budget
#print axioms MethbokeAddon.WeakFouriermanB.homogeneous_dissipation_square_integrable_of_fourier_budget
#check MethbokeAddon.WeakFouriermanB.homogeneous_physical_fourier_budget_to_serrin
#print axioms MethbokeAddon.WeakFouriermanB.homogeneous_physical_fourier_budget_to_serrin
#check MethbokeAddon.WeakFouriermanB.local_homogeneous_fourier_budget_to_serrin
#print axioms MethbokeAddon.WeakFouriermanB.local_homogeneous_fourier_budget_to_serrin
