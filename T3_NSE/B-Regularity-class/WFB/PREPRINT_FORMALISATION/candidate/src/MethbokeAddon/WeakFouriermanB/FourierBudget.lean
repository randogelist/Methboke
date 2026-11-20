import MethbokeAddon.WeakFouriermanB.PhysicalFourier
import SingularClosure.CriticalSerrinTime
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
The physical pre-continuation part of `Weak_Fourierman_B`.

The full Fourier sum is extended-nonnegative, so a divergent series cannot
silently acquire the default real `tsum` value zero. The time budget is a
`lintegral < infinity` assertion over the whole open front. No globally regular
solution wrapper, maximal-endpoint continuation theorem or gluing theorem is
assumed in the lemmas below. The result is the actual spatial L6 norm in time L4.

Prepared for external Lean 4.33.0 verification. No local compiler execution.
-/

set_option autoImplicit false

open Set MeasureTheory Filter SingularClosure
open scoped BigOperators ENNReal ContDiff

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- Squared full-mode time budget through the entire open front. -/
def FourierBudgetFinite (c : ℝ → FourierCoeff) (T : ℝ) : Prop :=
  (∫⁻ t in Ioo (0 : ℝ) T, ExtendedFourierEnstrophy (c t) ^ 2) < (⊤ : ℝ≥0∞)

/-- The pointwise physical Parseval identity transfers an extended Fourier
budget to integrability of the square of actual physical dissipation. -/
theorem dissipation_square_integrable_of_fourier_budget
    (μ : Measure ℝ) (u : ℝ → Field) (c : ℝ → FourierCoeff)
    (hD : AEStronglyMeasurable (fun t => physicalDissipation (u t)) μ)
    (hParseval : ∀ᵐ t ∂μ,
      physicalDissipation (u t) = (4 * Real.pi ^ 2) * FourierEnstrophy (c t))
    (hExtended : ∀ᵐ t ∂μ,
      ENNReal.ofReal (FourierEnstrophy (c t)) = ExtendedFourierEnstrophy (c t))
    (hbudget : (∫⁻ t, ExtendedFourierEnstrophy (c t) ^ 2 ∂μ) < (⊤ : ℝ≥0∞)) :
    Integrable (fun t => physicalDissipation (u t) ^ 2) μ := by
  have heq :
      (∫⁻ t, ENNReal.ofReal (physicalDissipation (u t) ^ 2) ∂μ) =
        ENNReal.ofReal ((4 * Real.pi ^ 2) ^ 2) *
          (∫⁻ t, ExtendedFourierEnstrophy (c t) ^ 2 ∂μ) := by
    calc
      _ = ∫⁻ t, ENNReal.ofReal ((4 * Real.pi ^ 2) ^ 2) *
          ExtendedFourierEnstrophy (c t) ^ 2 ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hParseval, hExtended] with t hp he
        rw [hp, mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
          ENNReal.ofReal_pow (fourierEnstrophy_nonneg (c t)) 2, he]
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  apply (lintegral_ofReal_ne_top_iff_integrable (hD.pow 2)
    (Eventually.of_forall fun t => sq_nonneg (physicalDissipation (u t)))).mp
  change (∫⁻ t, ENNReal.ofReal (physicalDissipation (u t) ^ 2) ∂μ) ≠
    (⊤ : ℝ≥0∞)
  rw [heq]
  exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbudget).ne

/-- Local physical Sobolev-to-Serrin integration for arbitrary time slices.
The proof uses the cached spatial theorem, with no global-flow hypothesis. -/
theorem local_serrin_of_energy_and_dissipation
    (μ : Measure ℝ) (u : ℝ → Field)
    (hregular : ∀ᵐ t ∂μ, ContDiff ℝ ∞ (u t) ∧ SpatialPeriodic (u t))
    (hmeas : AEStronglyMeasurable (fun t => criticalSpatialNorm 6 (u t)) μ)
    (hD : Integrable (fun t => physicalDissipation (u t) ^ 2) μ)
    (hE : Integrable (fun t => physicalEnergy (u t) ^ 2) μ) :
    MemLp (fun t => criticalSpatialNorm 6 (u t)) 4 μ := by
  obtain ⟨K, hK, hbound⟩ := CRITICAL_SMOOTH_L6_FOURTH_BOUND
  have hdom : Integrable (fun t => K *
      (9 * physicalDissipation (u t) ^ 2 + physicalEnergy (u t) ^ 2)) μ :=
    ((hD.const_mul 9).add hE).const_mul K
  have hfour : Integrable (fun t => criticalSpatialNorm 6 (u t) ^ 4) μ := by
    apply hdom.mono' (hmeas.pow 4)
    filter_upwards [hregular] with t ht
    change ‖criticalSpatialNorm 6 (u t) ^ 4‖ ≤
      K * (9 * physicalDissipation (u t) ^ 2 + physicalEnergy (u t) ^ 2)
    rw [Real.norm_of_nonneg (pow_nonneg (criticalSpatialNorm_nonneg 6 _) 4)]
    exact hbound (u t) ht.1 ht.2
  apply (integrable_norm_rpow_iff hmeas
    (by norm_num : (4 : ℝ≥0∞) ≠ 0)
    (by norm_num : (4 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))).mp
  have hnorm (t : ℝ) : ‖criticalSpatialNorm 6 (u t)‖ = criticalSpatialNorm 6 (u t) :=
    Real.norm_of_nonneg (criticalSpatialNorm_nonneg 6 _)
  have hpow (x : ℝ) : x ^ (4 : ℝ) = x ^ (4 : ℕ) := Real.rpow_ofNat x 4
  simpa only [ENNReal.toReal_ofNat, hnorm, hpow] using hfour

/-- A bounded actual kinetic energy has integrable square on a finite measure. -/
theorem physical_energy_square_integrable_of_bound
    (μ : Measure ℝ) [IsFiniteMeasure μ] (u : ℝ → Field) (E0 : ℝ)
    (hmeas : AEStronglyMeasurable (fun t => physicalEnergy (u t)) μ)
    (hbound : ∀ᵐ t ∂μ, physicalEnergy (u t) ≤ E0) :
    Integrable (fun t => physicalEnergy (u t) ^ 2) μ := by
  apply (integrable_const (E0 ^ 2) : Integrable (fun _ : ℝ => E0 ^ 2) μ).mono'
    (hmeas.pow 2)
  filter_upwards [hbound] with t ht
  change ‖physicalEnergy (u t) ^ 2‖ ≤ E0 ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hE0 : 0 ≤ physicalEnergy (u t) := by
    rw [physicalEnergy_eq_integral_norm_sq]
    exact integral_nonneg (fun x => sq_nonneg _)
  exact pow_le_pow_left₀ hE0 ht 2

/-- The complete local, pre-continuation implication: the full Fourier budget
gives the physical Serrin (4,6) norm on the SAME open front. The Parseval and
extended-sum hypotheses must describe the coefficients of these exact slices. -/
theorem local_serrin_of_fourier_budget
    (u : ℝ → Field) (c : ℝ → FourierCoeff) (T E0 : ℝ)
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, ContDiff ℝ ∞ (u t) ∧ SpatialPeriodic (u t))
    (hL6meas : AEStronglyMeasurable (fun t => criticalSpatialNorm 6 (u t))
      (volume.restrict (Ioo (0 : ℝ) T)))
    (hDmeas : AEStronglyMeasurable (fun t => physicalDissipation (u t))
      (volume.restrict (Ioo (0 : ℝ) T)))
    (hEmeas : AEStronglyMeasurable (fun t => physicalEnergy (u t))
      (volume.restrict (Ioo (0 : ℝ) T)))
    (hEnergy : ∀ t ∈ Ioo (0 : ℝ) T, physicalEnergy (u t) ≤ E0)
    (hParseval : ∀ t ∈ Ioo (0 : ℝ) T,
      physicalDissipation (u t) = (4 * Real.pi ^ 2) * FourierEnstrophy (c t))
    (hExtended : ∀ t ∈ Ioo (0 : ℝ) T,
      ENNReal.ofReal (FourierEnstrophy (c t)) = ExtendedFourierEnstrophy (c t))
    (hbudget : FourierBudgetFinite c T) :
    MemLp (fun t => criticalSpatialNorm 6 (u t)) 4
      (volume.restrict (Ioo (0 : ℝ) T)) := by
  have hmem : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) T)), t ∈ Ioo (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Ioo
  have hD := dissipation_square_integrable_of_fourier_budget
    (volume.restrict (Ioo (0 : ℝ) T)) u c hDmeas
    (hmem.mono fun t ht => hParseval t ht)
    (hmem.mono fun t ht => hExtended t ht) hbudget
  have hE := physical_energy_square_integrable_of_bound
    (volume.restrict (Ioo (0 : ℝ) T)) u E0 hEmeas
    (hmem.mono fun t ht => hEnergy t ht)
  exact local_serrin_of_energy_and_dissipation
    (volume.restrict (Ioo (0 : ℝ) T)) u
    (hmem.mono fun t ht => hregular t ht) hL6meas hD hE

/-- Actual physical coefficients of the same smooth slices supply both Parseval
and the full-series bridge. This is the physical Fourier-to-Serrin endpoint. -/
theorem physical_fourier_budget_to_serrin
    (u : ℝ → Field) (T E0 : ℝ)
    (hslices : ∀ t ∈ Ioo (0 : ℝ) T, SmoothSigmaZero (u t))
    (hL6meas : AEStronglyMeasurable (fun t => criticalSpatialNorm 6 (u t))
      (volume.restrict (Ioo (0 : ℝ) T)))
    (hDmeas : AEStronglyMeasurable (fun t => physicalDissipation (u t))
      (volume.restrict (Ioo (0 : ℝ) T)))
    (hEmeas : AEStronglyMeasurable (fun t => physicalEnergy (u t))
      (volume.restrict (Ioo (0 : ℝ) T)))
    (hEnergy : ∀ t ∈ Ioo (0 : ℝ) T, physicalEnergy (u t) ≤ E0)
    (hbudget : FourierBudgetFinite (fun t => datumFourierCoeff (u t)) T) :
    MemLp (fun t => criticalSpatialNorm 6 (u t)) 4
      (volume.restrict (Ioo (0 : ℝ) T)) := by
  apply local_serrin_of_fourier_budget u (fun t => datumFourierCoeff (u t)) T E0
    (fun t ht => ⟨(hslices t ht).smooth, (hslices t ht).periodic⟩)
    hL6meas hDmeas hEmeas hEnergy
  · intro t ht
    exact smoothSigmaZero_dissipation_eq_fourierEnstrophy (u t) (hslices t ht)
  · intro t ht
    exact ofReal_fourierEnstrophy_eq_extended (datumFourierCoeff (u t))
      (smoothSigmaZero_fourierEnstrophy_summable (u t) (hslices t ht))
  · exact hbudget

end
end MethbokeAddon.WeakFouriermanB

set_option pp.fullNames true

#check MethbokeAddon.WeakFouriermanB.dissipation_square_integrable_of_fourier_budget
#print axioms MethbokeAddon.WeakFouriermanB.dissipation_square_integrable_of_fourier_budget
#check MethbokeAddon.WeakFouriermanB.local_serrin_of_energy_and_dissipation
#print axioms MethbokeAddon.WeakFouriermanB.local_serrin_of_energy_and_dissipation
#check MethbokeAddon.WeakFouriermanB.physical_energy_square_integrable_of_bound
#print axioms MethbokeAddon.WeakFouriermanB.physical_energy_square_integrable_of_bound
#check MethbokeAddon.WeakFouriermanB.local_serrin_of_fourier_budget
#print axioms MethbokeAddon.WeakFouriermanB.local_serrin_of_fourier_budget
#check MethbokeAddon.WeakFouriermanB.physical_fourier_budget_to_serrin
#print axioms MethbokeAddon.WeakFouriermanB.physical_fourier_budget_to_serrin
