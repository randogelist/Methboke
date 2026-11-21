import SingularClosure.CriticalSmoothParseval
import SingularClosure.CriticalSerrinTime
import SingularClosure.SmoothDatumSobolev
import SingularClosure.PeriodicFourierInjective
import QuasiFeffermanB.PhysicalH1Admission
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
Physical Fourier normalization for Weak_Fourierman_B.

The real-valued infinite sum is used only with an explicit summability theorem.
The extended nonnegative sum retains infinity and is the budget-facing quantity.
Frequency zero is included with zero weight; all three vector components occur.
This file proves spatial identities. It asserts no endpoint continuation.
Prepared for the user's external pinned Lean 4.33.0 workflow; not locally run.
-/

set_option autoImplicit false
open Set Filter MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology

namespace MethbokeAddon.WeakFouriermanB
open SingularClosure
noncomputable section

def FourierEnstrophyTerm (c : FourierCoeff) (ki : FourierIndex) : ℝ :=
  (galerkinFreqSq ki.1 : ℝ) * Complex.normSq (c ki.1 ki.2)

def FourierEnstrophy (c : FourierCoeff) : ℝ :=
  ∑' ki : FourierIndex, FourierEnstrophyTerm c ki

def ExtendedFourierEnstrophy (c : FourierCoeff) : ℝ≥0∞ :=
  ∑' ki : FourierIndex, ENNReal.ofReal (FourierEnstrophyTerm c ki)

theorem fourierEnstrophyTerm_nonneg (c : FourierCoeff) (ki : FourierIndex) :
    0 ≤ FourierEnstrophyTerm c ki := by
  have hk : (0 : ℝ) ≤ (galerkinFreqSq ki.1 : ℝ) := by
    exact_mod_cast galerkinFreqSq_nonneg ki.1
  exact mul_nonneg hk (Complex.normSq_nonneg _)

theorem fourierEnstrophyTerm_zero_frequency (c : FourierCoeff) (i : Fin 3) :
    FourierEnstrophyTerm c (0, i) = 0 := by
  simp [FourierEnstrophyTerm, galerkinFreqSq]

theorem fourierEnstrophy_nonneg (c : FourierCoeff) :
    0 ≤ FourierEnstrophy c :=
  tsum_nonneg (fourierEnstrophyTerm_nonneg c)

theorem fourierEnstrophy_summable
    (c : FourierCoeff) (hzero : SpectralMeanZero c)
    (w : CriticalSobolev 2) (hw : criticalCoeff 2 w = c) :
    Summable (FourierEnstrophyTerm c) := by
  have hs : Summable (fun ki : FourierIndex =>
      laplacianFrequency ki.1 * Complex.normSq (c ki.1 ki.2)) := by
    simpa only [hw] using
      critical_H1_laplacian_summable w (by simpa only [hw] using hzero)
  have hscale : (2 * Real.pi) ^ 2 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hscaled := hs.mul_left (((2 * Real.pi) ^ 2)⁻¹)
  apply hscaled.congr
  intro ki
  simp only [FourierEnstrophyTerm, laplacianFrequency, ← mul_assoc,
    inv_mul_cancel₀ hscale, one_mul]

theorem ofReal_fourierEnstrophy_eq_extended
    (c : FourierCoeff) (hc : Summable (FourierEnstrophyTerm c)) :
    ENNReal.ofReal (FourierEnstrophy c) = ExtendedFourierEnstrophy c := by
  exact ENNReal.ofReal_tsum_of_nonneg (fourierEnstrophyTerm_nonneg c) hc

theorem extendedFourierEnstrophy_ne_top
    (c : FourierCoeff) (hc : Summable (FourierEnstrophyTerm c)) :
    ExtendedFourierEnstrophy c ≠ ⊤ := by
  rw [← ofReal_fourierEnstrophy_eq_extended c hc]
  exact ENNReal.ofReal_ne_top

theorem fourierEnstrophy_eq_modes_components
    (c : FourierCoeff) (hc : Summable (FourierEnstrophyTerm c)) :
    FourierEnstrophy c = ∑' k : Frequency,
      ∑ i : Fin 3, (galerkinFreqSq k : ℝ) * Complex.normSq (c k i) := by
  simpa only [FourierEnstrophy, FourierEnstrophyTerm, tsum_fintype] using hc.tsum_prod

theorem criticalH1_norm_sq_eq_fourierEnstrophy
    (c : FourierCoeff) (hzero : SpectralMeanZero c)
    (w : CriticalSobolev 2) (hw : criticalCoeff 2 w = c) :
    ‖w‖ ^ 2 = (4 * Real.pi ^ 2) * FourierEnstrophy c := by
  calc
    ‖w‖ ^ 2 = ∑' ki : FourierIndex,
        laplacianFrequency ki.1 * Complex.normSq (c ki.1 ki.2) := by
      rw [criticalSobolev_norm_sq, hw]
      exact tsum_congr (fun ki => critical_weight_two_laplacian c hzero ki.1 ki.2)
    _ = (2 * Real.pi) ^ 2 * FourierEnstrophy c := by
      simp only [laplacianFrequency, FourierEnstrophy, FourierEnstrophyTerm, mul_assoc]
      exact tsum_mul_left
    _ = (4 * Real.pi ^ 2) * FourierEnstrophy c := by ring

theorem smoothSynthesis_dissipation_eq_fourierEnstrophy
    (c : FourierCoeff)
    (hc : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i))
    (hreal : SpectralReality c) (hzero : SpectralMeanZero c)
    (w : CriticalSobolev 2) (hw : criticalCoeff 2 w = c) :
    physicalDissipation (smoothFourierSynthesis c) =
      (4 * Real.pi ^ 2) * FourierEnstrophy c := by
  rw [critical_smoothFourierSynthesis_dissipation_eq_norm_sq c hc hreal hzero w hw]
  exact criticalH1_norm_sq_eq_fourierEnstrophy c hzero w hw

theorem physicalH1_of_smooth_periodic
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    CriticalPhysicalH1 v (fderiv ℝ v) :=
  critical_smooth_physicalH1 v hv hp

theorem smoothFourierSynthesis_datum_eq
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    smoothFourierSynthesis (datumFourierCoeff v) = v := by
  have hr := ALL_SOBOLEV_IMP_RAPID_SCALAR (datumFourierCoeff v)
    (fun s => SMOOTH_DATUM_MEM_TORUS_SOBOLEV s v hv hp)
  exact datumFourierCoeff_injective_continuous_periodic _ _
    (smoothFourierSynthesis_contDiff _ hr).continuous hv.continuous
    (smoothFourierSynthesis_periodic _) hp
    (datumFourierCoeff_smoothFourierSynthesis _ hr (datumFourierCoeff_reality v))

theorem smoothSigmaZero_fourierEnstrophy_summable
    (v : Field) (hv : SmoothSigmaZero v) :
    Summable (FourierEnstrophyTerm (datumFourierCoeff v)) := by
  have hH1 := physicalH1_of_smooth_periodic v hv.smooth hv.periodic
  have hz := smoothSigmaZero_fourier_meanZero hv
  exact fourierEnstrophy_summable (datumFourierCoeff v) hz
    (QuasiFeffermanB.physicalH1SobolevDatum hH1 hz)
    (QuasiFeffermanB.physicalH1SobolevDatum_coeff hH1 hz)

theorem smoothSigmaZero_dissipation_eq_fourierEnstrophy
    (v : Field) (hv : SmoothSigmaZero v) :
    physicalDissipation v =
      (4 * Real.pi ^ 2) * FourierEnstrophy (datumFourierCoeff v) := by
  have hH1 := physicalH1_of_smooth_periodic v hv.smooth hv.periodic
  have hz := smoothSigmaZero_fourier_meanZero hv
  have hr := ALL_SOBOLEV_IMP_RAPID_SCALAR (datumFourierCoeff v)
    (fun s => SMOOTH_DATUM_MEM_TORUS_SOBOLEV s v hv.smooth hv.periodic)
  have h := smoothSynthesis_dissipation_eq_fourierEnstrophy (datumFourierCoeff v)
    hr (datumFourierCoeff_reality v) hz
    (QuasiFeffermanB.physicalH1SobolevDatum hH1 hz)
    (QuasiFeffermanB.physicalH1SobolevDatum_coeff hH1 hz)
  simpa only [smoothFourierSynthesis_datum_eq v hv.smooth hv.periodic] using h

end
end MethbokeAddon.WeakFouriermanB

set_option pp.fullNames true

#check MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_nonneg
#print axioms MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_nonneg
#check MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_zero_frequency
#print axioms MethbokeAddon.WeakFouriermanB.fourierEnstrophyTerm_zero_frequency
#check MethbokeAddon.WeakFouriermanB.fourierEnstrophy_nonneg
#print axioms MethbokeAddon.WeakFouriermanB.fourierEnstrophy_nonneg
#check MethbokeAddon.WeakFouriermanB.fourierEnstrophy_summable
#print axioms MethbokeAddon.WeakFouriermanB.fourierEnstrophy_summable
#check MethbokeAddon.WeakFouriermanB.ofReal_fourierEnstrophy_eq_extended
#print axioms MethbokeAddon.WeakFouriermanB.ofReal_fourierEnstrophy_eq_extended
#check MethbokeAddon.WeakFouriermanB.extendedFourierEnstrophy_ne_top
#print axioms MethbokeAddon.WeakFouriermanB.extendedFourierEnstrophy_ne_top
#check MethbokeAddon.WeakFouriermanB.fourierEnstrophy_eq_modes_components
#print axioms MethbokeAddon.WeakFouriermanB.fourierEnstrophy_eq_modes_components
#check MethbokeAddon.WeakFouriermanB.criticalH1_norm_sq_eq_fourierEnstrophy
#print axioms MethbokeAddon.WeakFouriermanB.criticalH1_norm_sq_eq_fourierEnstrophy
#check MethbokeAddon.WeakFouriermanB.smoothSynthesis_dissipation_eq_fourierEnstrophy
#print axioms MethbokeAddon.WeakFouriermanB.smoothSynthesis_dissipation_eq_fourierEnstrophy
#check MethbokeAddon.WeakFouriermanB.physicalH1_of_smooth_periodic
#print axioms MethbokeAddon.WeakFouriermanB.physicalH1_of_smooth_periodic
#check MethbokeAddon.WeakFouriermanB.smoothFourierSynthesis_datum_eq
#print axioms MethbokeAddon.WeakFouriermanB.smoothFourierSynthesis_datum_eq
#check MethbokeAddon.WeakFouriermanB.smoothSigmaZero_fourierEnstrophy_summable
#print axioms MethbokeAddon.WeakFouriermanB.smoothSigmaZero_fourierEnstrophy_summable
#check MethbokeAddon.WeakFouriermanB.smoothSigmaZero_dissipation_eq_fourierEnstrophy
#print axioms MethbokeAddon.WeakFouriermanB.smoothSigmaZero_dissipation_eq_fourierEnstrophy
