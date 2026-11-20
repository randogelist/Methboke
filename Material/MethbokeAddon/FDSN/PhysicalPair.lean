import MethbokeAddon.FDSN.FourierPair
import SingularClosure.SmoothDatumSobolev
import SingularClosure.SobolevSmoothRealization
import SingularClosure.PeriodicFourierInjective

/-!
# The actual smooth periodic field obtained by one conjugate-pair rotation

The field uses the existing convergent physical Fourier synthesis and its
coefficient-recovery theorem. Its input is the actual cube Fourier integral
of a smooth periodic velocity. No zero-mean assumption is imposed.

The general solenoidality proof below is the native InitialFourier proof
with its unused mean-zero field removed. No unproved Fourier law is assumed.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace MethbokeAddon.FDSN

open SingularClosure

noncomputable section

/-- Physical divergence freedom supplies spectral solenoidality, with the
spatial mean retained. -/
theorem smoothPeriodic_fourier_solenoidal {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (hd : ∀ x : Vec, divergence v x = 0) :
    SpectralSolenoidal (datumFourierCoeff v) := by
  intro k
  have hzero := integral_unitCube_divergence_eq_zero
    (fun i => datumFourierIntegrand v k i)
    (fun i => datumFourierIntegrand_contDiff hv k i)
    (fun i x => datumFourierIntegrand_periodic hp k i x i)
  have hsum (x : Vec) :
      (∑ i : Fin 3, fderiv ℝ (datumFourierIntegrand v k i) x (unitVector i)) =
        -(∑ i : Fin 3, derivativeSymbol i k * datumFourierIntegrand v k i x) := by
    simp_rw [datumFourierIntegrand_coordinateDerivative (hv.differentiable (by simp))]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum]
    change star (fourierCharacter k x) * (divergence v x : ℂ) - _ = _
    rw [hd x]
    simp
  simp_rw [hsum] at hzero
  rw [integral_neg] at hzero
  have hcoeff : (∑ i : Fin 3, derivativeSymbol i k * datumFourierCoeff v k i) = 0 := by
    have h := neg_eq_zero.mp hzero
    rw [integral_finsetSum Finset.univ (fun i _ =>
      (datumFourierIntegrand_integrableOn hv.continuous k i).const_mul
        (derivativeSymbol i k))] at h
    simpa only [integral_const_mul, datumFourierCoeff] using h
  let C : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hfactor :
      (∑ i : Fin 3, derivativeSymbol i k * datumFourierCoeff v k i) =
        C * ∑ i : Fin 3, (k i : ℂ) * datumFourierCoeff v k i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [derivativeSymbol, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_intCast, C]
    ring
  have hC : C ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact Complex.I_ne_zero
  rw [hfactor] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left hC

theorem smoothPeriodic_fourier_rapid {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (i : Fin 3) :
    RapidScalarFourier (fun k => datumFourierCoeff v k i) :=
  ALL_SOBOLEV_IMP_RAPID_SCALAR (datumFourierCoeff v)
    (fun s => SMOOTH_DATUM_MEM_TORUS_SOBOLEV s v hv hp) i

theorem pairRotate_rapid (a : Frequency) {z : ℂ} (hz : ‖z‖ = 1)
    {c : FourierCoeff} (hc : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i))
    (i : Fin 3) : RapidScalarFourier (fun k => pairRotate a z c k i) := by
  intro m
  simpa only [pairRotate_component_norm a hz] using hc i m

/-- Actual smooth Fourier reconstruction of a smooth periodic field. -/
theorem smoothPeriodic_fourier_reconstruction {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    smoothFourierSynthesis (datumFourierCoeff v) = v := by
  have hr := smoothPeriodic_fourier_rapid hv hp
  exact datumFourierCoeff_injective_continuous_periodic _ _
    (smoothFourierSynthesis_contDiff _ hr).continuous hv.continuous
    (smoothFourierSynthesis_periodic _) hp
    (datumFourierCoeff_smoothFourierSynthesis _ hr (datumFourierCoeff_reality v))

/-- The actual real periodic field, with a single conjugate coefficient pair
rotated and all remaining modes retained. -/
def physicalPairRotation (a : Frequency) (z : ℂ) (v : Field) : Field :=
  smoothFourierSynthesis (pairRotate a z (datumFourierCoeff v))

theorem physicalPairRotation_smooth (a : Frequency) {z : ℂ} (hz : ‖z‖ = 1)
    {v : Field} (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    ContDiff ℝ ∞ (physicalPairRotation a z v) :=
  smoothFourierSynthesis_contDiff _
    (pairRotate_rapid a hz (smoothPeriodic_fourier_rapid hv hp))

theorem physicalPairRotation_periodic (a : Frequency) (z : ℂ) (v : Field) :
    SpatialPeriodic (physicalPairRotation a z v) :=
  smoothFourierSynthesis_periodic _

theorem physicalPairRotation_coeff {a : Frequency} (ha : a ≠ 0)
    {z : ℂ} (hz : ‖z‖ = 1) {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    datumFourierCoeff (physicalPairRotation a z v) =
      pairRotate a z (datumFourierCoeff v) :=
  datumFourierCoeff_smoothFourierSynthesis _
    (pairRotate_rapid a hz (smoothPeriodic_fourier_rapid hv hp))
    (pairRotate_reality ha z (datumFourierCoeff_reality v))

theorem physicalPairRotation_divergence_free (a : Frequency)
    {z : ℂ} (hz : ‖z‖ = 1) {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (hd : ∀ x : Vec, divergence v x = 0) :
    ∀ x : Vec, divergence (physicalPairRotation a z v) x = 0 :=
  smoothFourierSynthesis_divergence_free _
    (pairRotate_rapid a hz (smoothPeriodic_fourier_rapid hv hp))
    (pairRotate_solenoidal a z (smoothPeriodic_fourier_solenoidal hv hp hd))

theorem physicalPairRotation_one (a : Frequency) {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    physicalPairRotation a 1 v = v := by
  unfold physicalPairRotation
  rw [pairRotate_one]
  exact smoothPeriodic_fourier_reconstruction hv hp

theorem physicalPairRotation_mean_coeff {a : Frequency} (ha : a ≠ 0)
    {z : ℂ} (hz : ‖z‖ = 1) {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    datumFourierCoeff (physicalPairRotation a z v) 0 = datumFourierCoeff v 0 := by
  rw [physicalPairRotation_coeff ha hz hv hp]
  exact pairRotate_mean ha z (datumFourierCoeff v)

theorem physicalPairRotation_mean {a : Frequency} (ha : a ≠ 0)
    {z : ℂ} (hz : ‖z‖ = 1) {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    spatialMean (physicalPairRotation a z v) = spatialMean v := by
  have hint : IntegrableOn v unitCube volume :=
    hv.continuous.continuousOn.integrableOn_compact isCompact_unitCube
  have hint' : IntegrableOn (physicalPairRotation a z v) unitCube volume :=
    (physicalPairRotation_smooth a hz hv hp).continuous.continuousOn.integrableOn_compact
      isCompact_unitCube
  ext i
  apply Complex.ofReal_injective
  rw [← datumFourierCoeff_zero hint' i, ← datumFourierCoeff_zero hint i]
  exact congrFun (physicalPairRotation_mean_coeff ha hz hv hp) i

theorem physicalPairRotation_observable_norm {a : Frequency} (ha : a ≠ 0)
    {z : ℂ} (hz : ‖z‖ = 1) {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (k : Frequency) (L : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) :
    ‖L (datumFourierCoeff (physicalPairRotation a z v) k)‖ =
      ‖L (datumFourierCoeff v k)‖ := by
  rw [physicalPairRotation_coeff ha hz hv hp]
  exact pairRotate_observable_norm a hz (datumFourierCoeff v) k L

/-- A constructed actual spatial endpoint, preserving smoothness, periodicity,
divergence freedom, the physical mean and every linear modal-observation norm. -/
theorem PHYSICAL_PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_DATA
    {a : Frequency} (ha : a ≠ 0) {z : ℂ} (hz : ‖z‖ = 1)
    {v : Field} (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (hd : ∀ x : Vec, divergence v x = 0) :
    ContDiff ℝ ∞ (physicalPairRotation a z v) ∧
    SpatialPeriodic (physicalPairRotation a z v) ∧
    (∀ x : Vec, divergence (physicalPairRotation a z v) x = 0) ∧
    spatialMean (physicalPairRotation a z v) = spatialMean v ∧
    (∀ k : Frequency, ∀ L : (Fin 3 → ℂ) →ₗ[ℂ] ℂ,
      ‖L (datumFourierCoeff (physicalPairRotation a z v) k)‖ =
        ‖L (datumFourierCoeff v k)‖) := by
  exact ⟨physicalPairRotation_smooth a hz hv hp,
    physicalPairRotation_periodic a z v,
    physicalPairRotation_divergence_free a hz hv hp hd,
    physicalPairRotation_mean ha hz hv hp,
    fun k L => physicalPairRotation_observable_norm ha hz hv hp k L⟩

end

end MethbokeAddon.FDSN
