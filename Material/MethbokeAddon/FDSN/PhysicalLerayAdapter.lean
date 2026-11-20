import MethbokeAddon.FDSN.FamilyContracts
import MethbokeAddon.FDSN.PhysicalPair
import MethbokeAddon.FDSN.PairForceUniqueness
import SingularClosure.InfiniteFourierPressure
import SingularClosure.FourierSobolevOperators
import SingularClosure.SmoothFourierLaplacian

/-!
# Physical meaning of projected-force separation

This optional adapter reconstructs the actual periodic Leray projection from
its native Fourier symbol. It retains the zero mode, identifies the physical
field as the input plus the native pressure gradient, and turns a separating
projected Fourier coefficient into a nonzero physical projected force
difference. It is not a dependency of the original FDSN candidate.
-/

set_option autoImplicit false

noncomputable section

open Set SingularClosure
open MethbokeAddon.FeffermanFamily
open scoped ContDiff

namespace MethbokeAddon.FDSN

def physicalLerayProjection (v : Field) : Field :=
  smoothFourierSynthesis (lerayFourierCoeff (datumFourierCoeff v))

theorem physicalLerayProjection_rapid {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (i : Fin 3) :
    RapidScalarFourier (fun k => coefficientLeray k (datumFourierCoeff v k) i) := by
  apply ALL_SOBOLEV_IMP_RAPID_SCALAR (lerayFourierCoeff (datumFourierCoeff v)) _ i
  intro s
  exact torusSobolevLeray_mem s (smoothDatumSobolev s v hv hp)

theorem physicalLerayProjection_smooth {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    ContDiff ℝ ∞ (physicalLerayProjection v) :=
  smoothFourierSynthesis_contDiff _ (physicalLerayProjection_rapid hv hp)

theorem physicalLerayProjection_periodic (v : Field) :
    SpatialPeriodic (physicalLerayProjection v) :=
  smoothFourierSynthesis_periodic _

theorem physicalLerayProjection_coeff {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    datumFourierCoeff (physicalLerayProjection v) =
      fun k => coefficientLeray k (datumFourierCoeff v k) :=
  datumFourierCoeff_smoothFourierSynthesis _ (physicalLerayProjection_rapid hv hp)
    (lerayFourierCoeff_reality _ (datumFourierCoeff_reality v))

theorem physicalLerayProjection_zero_mode {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    datumFourierCoeff (physicalLerayProjection v) 0 = datumFourierCoeff v 0 := by
  rw [physicalLerayProjection_coeff hv hp]
  simp [coefficientLeray]

/-- The synthesized projection is the actual Helmholtz correction of the
physical field. The native pressure convention gives `v + gradient π`. -/
theorem physicalLerayProjection_helmholtz {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    physicalLerayProjection v =
      v + SingularClosure.gradient (infiniteTransportPressure (datumFourierCoeff v)) := by
  funext x
  have hrec := infiniteTransportPressure_recovery (datumFourierCoeff v)
    (smoothPeriodic_fourier_rapid hv hp) x
  rw [smoothPeriodic_fourier_reconstruction hv hp] at hrec
  exact hrec.symm

theorem physicalLerayProjection_divergence_free {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (x : Vec) :
    divergence (physicalLerayProjection v) x = 0 :=
  smoothFourierSynthesis_divergence_free _ (physicalLerayProjection_rapid hv hp)
    (lerayFourierCoeff_solenoidal _) x

theorem datumFourierCoeff_sub_continuous (v w : Field)
    (hv : Continuous v) (hw : Continuous w) :
    datumFourierCoeff (v - w) = datumFourierCoeff v - datumFourierCoeff w := by
  have hsub : v - w = v + (-1 : ℝ) • w := by
    simp only [neg_one_smul, sub_eq_add_neg]
  rw [hsub, datumFourierCoeff_add _ _ hv (hw.const_smul (-1)),
    datumFourierCoeff_real_smul]
  simp [sub_eq_add_neg]

theorem physicalLerayProjection_ne_zero_of_coefficient_ne_zero
    {v : Field} (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    {k : Frequency} {i : Fin 3}
    (hne : coefficientLeray k (datumFourierCoeff v k) i ≠ 0) :
    physicalLerayProjection v ≠ 0 := by
  intro hzero
  have hcoeff := congrFun (congrFun (physicalLerayProjection_coeff hv hp) k) i
  rw [hzero] at hcoeff
  apply hne
  simpa [datumFourierCoeff, datumFourierIntegrand] using hcoeff.symm

/-- The canonical coefficient-separation clause entails a literal nonzero
physical Leray projection of each distinct pair of force histories. -/
theorem projectedForceSeparation_physical
    {T ε : ℝ} {G : ℝ → Velocity}
    (hG : ∀ lambda : ℝ, |lambda| < ε → AdmissiblePeriodicForce (G lambda))
    (hsep : ProjectedForceSeparation T ε G) :
    ∀ lambda eta : ℝ, |lambda| < ε → |eta| < ε → lambda ≠ eta →
      ∃ t ∈ Ico (0 : ℝ) T, ∃ x : Vec,
        physicalLerayProjection ((G lambda - G eta) t) x ≠ 0 := by
  classical
  intro lambda eta hlambda heta hne
  obtain ⟨t, ht, k, i, hki⟩ := hsep lambda eta hlambda heta hne
  have hl : ContDiff ℝ ∞ (G lambda t) :=
    (hG lambda hlambda).smooth.comp (contDiff_const.prodMk contDiff_id)
  have he : ContDiff ℝ ∞ (G eta t) :=
    (hG eta heta).smooth.comp (contDiff_const.prodMk contDiff_id)
  have hp : SpatialPeriodic ((G lambda - G eta) t) := by
    intro x j
    change G lambda t (x + unitVector j) - G eta t (x + unitVector j) =
      G lambda t x - G eta t x
    rw [(hG lambda hlambda).periodic t x j, (hG eta heta).periodic t x j]
  have hcoeff : coefficientLeray k (datumFourierCoeff ((G lambda - G eta) t) k) i ≠ 0 := by
    change coefficientLeray k (datumFourierCoeff (G lambda t - G eta t) k) i ≠ 0
    rw [datumFourierCoeff_sub_continuous _ _ hl.continuous he.continuous]
    change coefficientLeray k (datumFourierCoeff (G lambda t) k -
      datumFourierCoeff (G eta t) k) i ≠ 0
    rw [coefficientLeray_sub_arg]
    exact sub_ne_zero.mpr hki
  have hfield : physicalLerayProjection ((G lambda - G eta) t) ≠ 0 :=
    physicalLerayProjection_ne_zero_of_coefficient_ne_zero (hl.sub he) hp hcoeff
  have hx : ∃ x : Vec, physicalLerayProjection ((G lambda - G eta) t) x ≠ 0 :=
    not_forall.mp (fun hz => hfield (funext hz))
  obtain ⟨x, hx⟩ := hx
  exact ⟨t, ht, x, hx⟩

end MethbokeAddon.FDSN
