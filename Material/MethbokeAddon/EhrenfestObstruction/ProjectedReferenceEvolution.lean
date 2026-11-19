import MethbokeAddon.EhrenfestObstruction.ReferenceCoefficientEvolution
import MethbokeAddon.EhrenfestObstruction.PressureFourier
import SingularClosure.FourierSobolevOperators
import SingularClosure.SmoothFourierLaplacian

/-!
The pressure-free Fourier equation of the actual smooth reference field.
Every term is the physical Fourier integral or the literal native Leray map.
No projected-equation certificate is taken as a hypothesis.
Prepared source only; external cached compilation and auditing are required.
-/

set_option autoImplicit false

open Set SingularClosure
open MethbokeAddon.WeakFouriermanB
open scoped ContDiff

namespace MethbokeAddon.EhrenfestObstruction
noncomputable section

/-- Fourier transformation and Leray projection of the literal physical NSE. -/
theorem initial_front_projected_fourier_rhs
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (k : Frequency) (i : Fin 3) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) :
    datumFourierCoeff (timeDerivative u t) k i =
      -((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) *
          datumFourierCoeff (u t) k i -
        coefficientLeray k (datumFourierCoeff (convection (u t)) k) i := by
  have hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (localFrontSpacetime S) :=
    H.velocity_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)
  have hus := initial_front_smooth_slices ν S a u p H t ⟨ht.1.le, ht.2⟩
  have hdt : Continuous (timeDerivative u t) :=
    (local_timeDerivative_continuousOn u S hu).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ht)
  have hconv : Continuous (convection (u t)) :=
    (initial_convection_continuousOn u S H.velocity_smooth).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨ht.1.le, ht.2⟩)
  have hps : ContDiff ℝ ∞ (p t) := by
    rw [← contDiffOn_univ]
    exact H.pressure_smooth.comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ⟨ht.1.le, ht.2⟩)
  have hgrad : Continuous (SingularClosure.gradient (p t)) :=
    criticalWeak_gradient_continuous _ hps
  have hfield : timeDerivative u t + convection (u t) + SingularClosure.gradient (p t) =
      ν • laplacian (u t) :=
    funext (fun x => H.equation t ⟨ht.1.le, ht.2⟩ x)
  have hfourier : datumFourierCoeff (timeDerivative u t) +
      datumFourierCoeff (convection (u t)) + datumFourierCoeff (SingularClosure.gradient (p t)) =
      (ν : ℂ) • laplacianCoefficient (datumFourierCoeff (u t)) := by
    calc
      _ = datumFourierCoeff
          (timeDerivative u t + convection (u t) + SingularClosure.gradient (p t)) := by
        rw [datumFourierCoeff_add _ _ (hdt.add hconv) hgrad,
          datumFourierCoeff_add _ _ hdt hconv]
      _ = _ := by
        rw [hfield, datumFourierCoeff_real_smul,
          datumFourierCoeff_laplacian (u t) hus.smooth hus.periodic]
  have hFk := congrArg (fun c : FourierCoeff => coefficientLeray k (c k)) hfourier
  change coefficientLeray k
      (datumFourierCoeff (timeDerivative u t) k + datumFourierCoeff (convection (u t)) k +
        datumFourierCoeff (SingularClosure.gradient (p t)) k) =
      coefficientLeray k
        ((ν : ℂ) • (-(laplacianFrequency k : ℂ) • datumFourierCoeff (u t) k)) at hFk
  rw [coefficientLeray_add_arg, coefficientLeray_add_arg,
    initial_front_timeDerivative_fourier_leray ν S a u p H t ht k,
    datumFourierCoeff_gradient_leray_eq_zero (p t) hps
      (H.pressure_periodic t ⟨ht.1.le, ht.2⟩) k,
    coefficientLeray_smul_arg, coefficientLeray_smul_arg,
    coefficientLeray_eq_of_solenoidal k _ (smoothSigmaZero_fourier_solenoidal hus k)] at hFk
  have hmode := congrArg (fun v : Fin 3 → ℂ => v i) hFk
  change datumFourierCoeff (timeDerivative u t) k i +
      coefficientLeray k (datumFourierCoeff (convection (u t)) k) i + 0 =
      (ν : ℂ) * (-(laplacianFrequency k : ℂ) * datumFourierCoeff (u t) k i) at hmode
  simp only [add_zero] at hmode
  apply eq_sub_iff_add_eq.mpr
  calc
    _ = (ν : ℂ) * (-(laplacianFrequency k : ℂ) * datumFourierCoeff (u t) k i) := hmode
    _ = _ := by
      simp only [laplacianFrequency, Complex.ofReal_mul]
      ring

/-- The actual reference coefficient solves the pressure-free Fourier NSE. -/
theorem initial_front_projected_fourier_hasDerivAt
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (k : Frequency) (i : Fin 3) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) :
    HasDerivAt (fun r => datumFourierCoeff (u r) k i)
      (-((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) *
          datumFourierCoeff (u t) k i -
        coefficientLeray k (datumFourierCoeff (convection (u t)) k) i) t := by
  rw [← initial_front_projected_fourier_rhs ν S a u p H k i t ht]
  exact initial_front_datumFourierCoeff_hasDerivAt ν S a u p H k i t ht

/-- Projection at the same literal finite cutoff commutes with reference time differentiation. -/
theorem initial_front_cutoff_fourier_hasDerivAt
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (N : ℕ) (k : Frequency) (i : Fin 3) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) :
    HasDerivAt (fun r => cutoffCoeff N (datumFourierCoeff (u r)) k i)
      (cutoffCoeff N (fun q j =>
        -((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq q : ℝ) : ℝ) : ℂ) *
            datumFourierCoeff (u t) q j -
          coefficientLeray q (datumFourierCoeff (convection (u t)) q) j) k i) t := by
  by_cases hk : k ∈ cutoffModes N
  · simpa only [cutoffCoeff, if_pos hk] using
      initial_front_projected_fourier_hasDerivAt ν S a u p H k i t ht
  · simpa only [cutoffCoeff, if_neg hk] using hasDerivAt_const t (0 : ℂ)

/-- The actual projected reference coefficient is continuous up to time zero. -/
theorem initial_front_cutoff_fourier_continuousOn_Icc
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (N : ℕ) (k : Frequency) (i : Fin 3) (T : ℝ) (hTS : T < S) :
    ContinuousOn (fun t => cutoffCoeff N (datumFourierCoeff (u t)) k i)
      (Icc (0 : ℝ) T) := by
  by_cases hk : k ∈ cutoffModes N
  · simpa only [cutoffCoeff, if_pos hk] using
      initial_front_datumFourierCoeff_continuousOn_Icc ν S a u p H k i T hTS
  · simpa only [cutoffCoeff, if_neg hk] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℂ)) (Icc (0 : ℝ) T))

end
end MethbokeAddon.EhrenfestObstruction
