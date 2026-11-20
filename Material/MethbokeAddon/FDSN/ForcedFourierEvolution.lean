import MethbokeAddon.FDSN.Contracts
import MethbokeAddon.FDSN.PhysicalPair
import MethbokeAddon.FDSN.TriadCancellation
import MethbokeAddon.FDSN.ModalEnergy
import MethbokeAddon.EhrenfestObstruction.ReferenceCoefficientEvolution
import MethbokeAddon.EhrenfestObstruction.PressureFourier
import SingularClosure.SmoothFourierLaplacian
import SingularClosure.FourierSobolevOperators
import Mathlib.Tactic.LinearCombination

/-!
# Actual forced preterminal Fourier evolution

Every identity is derived from the literal physical PDE, local smoothness,
periodicity and divergence freedom. The fields, mean and arbitrary terminal
time are retained. The final per-mode energy inequality is the finite-sum
entry point for the active-triad contradiction.
-/

set_option autoImplicit false

noncomputable section
open Set Filter SingularClosure
open MethbokeAddon.WeakFouriermanB MethbokeAddon.EhrenfestObstruction
open scoped BigOperators ContDiff Topology

namespace MethbokeAddon.FDSN

theorem PreterminalNSE.velocity_slice_smooth
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) : ContDiff ℝ ∞ (u t) :=
  local_spatial_slice_contDiff u T
    (H.velocity_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)) t ht

theorem PreterminalNSE.pressure_slice_smooth
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) : ContDiff ℝ ∞ (p t) := by
  have hlocal : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2)
      (localFrontSpacetime T) :=
    H.pressure_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hj := hlocal.contDiffAt ((localFrontSpacetime_isOpen T).mem_nhds
    (show (t, x) ∈ localFrontSpacetime T from ht))
  simpa only [Function.comp_def] using hj.comp x (contDiff_prodMk_right t).contDiffAt

theorem PreterminalNSE.fourier_solenoidal
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    SpectralSolenoidal (datumFourierCoeff (u t)) :=
  smoothPeriodic_fourier_solenoidal (H.velocity_slice_smooth t ht)
    (H.velocity_periodic t ⟨ht.1.le, ht.2⟩)
    (H.divergence_free t ⟨ht.1.le, ht.2⟩)

def PreterminalNSE.sobolevSlice
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) : TorusSobolev 0 :=
  smoothDatumSobolev 0 (u t) (H.velocity_slice_smooth t ht)
    (H.velocity_periodic t ⟨ht.1.le, ht.2⟩)

theorem PreterminalNSE.sobolevSlice_coeff
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    (H.sobolevSlice t ht).val = datumFourierCoeff (u t) := rfl

theorem PreterminalNSE.convection_coeff
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    datumFourierCoeff (convection (u t)) =
      fullTransportCoefficients (H.sobolevSlice t ht) := by
  have hv := H.velocity_slice_smooth t ht
  have hp := H.velocity_periodic t ⟨ht.1.le, ht.2⟩
  have hc := smoothFourierSynthesis_convection_coeff (H.sobolevSlice t ht)
    (fun s => SMOOTH_DATUM_MEM_TORUS_SOBOLEV s (u t) hv hp)
    (datumFourierCoeff_reality (u t)) (H.fourier_solenoidal t ht)
  simpa only [PreterminalNSE.sobolevSlice_coeff,
    smoothPeriodic_fourier_reconstruction hv hp] using hc

theorem PreterminalNSE.fourierCoeff_hasDerivAt
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (k : Frequency) (i : Fin 3) :
    HasDerivAt (fun r => datumFourierCoeff (u r) k i)
      (datumFourierCoeff (timeDerivative u t) k i) t :=
  local_datumFourierCoeff_hasDerivAt u T
    (H.velocity_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)) k i t ht

theorem PreterminalNSE.timeDerivative_fourier_solenoidal
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    SpectralSolenoidal (datumFourierCoeff (timeDerivative u t)) := by
  intro k
  have hj (j : Fin 3) := (H.fourierCoeff_hasDerivAt t ht k j).const_mul (k j : ℂ)
  have hsum : HasDerivAt
      (fun r => ∑ j : Fin 3, (k j : ℂ) * datumFourierCoeff (u r) k j)
      (∑ j : Fin 3, (k j : ℂ) * datumFourierCoeff (timeDerivative u t) k j) t := by
    simpa only [Fin.sum_univ_three, Pi.add_apply] using! ((hj 0).add (hj 1)).add (hj 2)
  have hzero : HasDerivAt (fun _ : ℝ => (0 : ℂ))
      (∑ j : Fin 3, (k j : ℂ) * datumFourierCoeff (timeDerivative u t) k j) t := by
    apply hsum.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact (H.fourier_solenoidal r hr k).symm
  exact hzero.unique (hasDerivAt_const t (0 : ℂ))

/-- Taking literal cube Fourier integrals of the actual forced equation. -/
theorem PreterminalNSE.fourier_balance
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (hF : Continuous (F t)) (k : Frequency) :
    datumFourierCoeff (timeDerivative u t) k +
        fullTransportCoefficients (H.sobolevSlice t ht) k +
        (fun i => derivativeSymbol i k * scalarPressureFourierCoeff (p t) k) =
      (ν : ℂ) • laplacianCoefficient (datumFourierCoeff (u t)) k +
        datumFourierCoeff (F t) k := by
  have hv := H.velocity_slice_smooth t ht
  have hp := H.pressure_slice_smooth t ht
  have hper := H.velocity_periodic t ⟨ht.1.le, ht.2⟩
  have hpper := H.pressure_periodic t ⟨ht.1.le, ht.2⟩
  have huLocal : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (localFrontSpacetime T) := H.velocity_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)
  have hud : Continuous (timeDerivative u t) :=
    (local_timeDerivative_continuousOn u T huLocal).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ht)
  have hconv : Continuous (convection (u t)) := convection_continuous hv
  have hgrad : Continuous (SingularClosure.gradient (p t)) := criticalWeak_gradient_continuous _ hp
  have hlap : Continuous (laplacian (u t)) := (laplacian_contDiff _ hv).continuous
  have heq : timeDerivative u t + convection (u t) + SingularClosure.gradient (p t) =
      ν • laplacian (u t) + F t := funext (H.equation t ⟨ht.1.le, ht.2⟩)
  have hc := congrArg datumFourierCoeff heq
  rw [datumFourierCoeff_add _ _ (hud.add hconv) hgrad,
    datumFourierCoeff_add _ _ hud hconv,
    datumFourierCoeff_add _ _ (hlap.const_smul ν) hF,
    datumFourierCoeff_real_smul, datumFourierCoeff_laplacian _ hv hper,
    H.convection_coeff t ht, datumFourierCoeff_gradient _ hp hpper] at hc
  exact congrFun hc k

/-- Pressure elimination with the native zero-mode-preserving Leray symbol. -/
theorem PreterminalNSE.projected_fourier_balance
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (hF : Continuous (F t)) (k : Frequency) :
    datumFourierCoeff (timeDerivative u t) k +
        coefficientLeray k (fullTransportCoefficients (H.sobolevSlice t ht) k) =
      (ν : ℂ) • laplacianCoefficient (datumFourierCoeff (u t)) k +
        coefficientLeray k (datumFourierCoeff (F t) k) := by
  have hd : coefficientLeray k (datumFourierCoeff (timeDerivative u t) k) =
      datumFourierCoeff (timeDerivative u t) k :=
    coefficientLeray_eq_of_solenoidal k _ (H.timeDerivative_fourier_solenoidal t ht k)
  have hl : coefficientLeray k (laplacianCoefficient (datumFourierCoeff (u t)) k) =
      laplacianCoefficient (datumFourierCoeff (u t)) k := by
    change coefficientLeray k (-(laplacianFrequency k : ℂ) • datumFourierCoeff (u t) k) =
      -(laplacianFrequency k : ℂ) • datumFourierCoeff (u t) k
    rw [coefficientLeray_smul_arg,
      coefficientLeray_eq_of_solenoidal k _ (H.fourier_solenoidal t ht k)]
  have he := congrArg (coefficientLeray k) (H.fourier_balance t ht hF k)
  simpa only [coefficientLeray_add_arg, hd,
    coefficientLeray_derivativeSymbol_mul_eq_zero, coefficientLeray_smul_arg, hl, add_zero] using he

/-- The literal coefficient curve satisfies the projected forced ODE. -/
theorem PreterminalNSE.projected_fourier_hasDerivAt
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (hF : Continuous (F t))
    (k : Frequency) (i : Fin 3) :
    HasDerivAt (fun r => datumFourierCoeff (u r) k i)
      (-((ν * laplacianFrequency k : ℝ) : ℂ) * datumFourierCoeff (u t) k i -
        coefficientLeray k (fullTransportCoefficients (H.sobolevSlice t ht) k) i +
        coefficientLeray k (datumFourierCoeff (F t) k) i) t := by
  have he := congrFun (H.projected_fourier_balance t ht hF k) i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, laplacianCoefficient] at he
  have hd : datumFourierCoeff (timeDerivative u t) k i =
      -((ν * laplacianFrequency k : ℝ) : ℂ) * datumFourierCoeff (u t) k i -
        coefficientLeray k (fullTransportCoefficients (H.sobolevSlice t ht) k) i +
        coefficientLeray k (datumFourierCoeff (F t) k) i := by
    push_cast
    linear_combination he
  rw [← hd]
  exact H.fourierCoeff_hasDerivAt t ht k i

theorem triad_free_projected_modal_transfer_zero
    (c : TorusSobolev 0) (hreal : SpectralReality c.val)
    (hsol : SpectralSolenoidal c.val) (htriad : ¬ HasActiveNoncollinearTriad c.val)
    (k : Frequency) (i : Fin 3) :
    (star (c.val k i) * coefficientLeray k (fullTransportCoefficients c k) i).re = 0 := by
  classical
  by_cases hout : c.val k = 0
  · have hi : c.val k i = 0 := congrFun hout i
    simp [hi]
  have he : fullTransportCoefficients c k = meanTransportFactor c.val k • c.val k := by
    funext j
    exact fullTransportCoefficients_eq_mean c hsol htriad k j hout
  rw [he, coefficientLeray_smul_arg,
    coefficientLeray_eq_of_solenoidal k _ (hsol k)]
  exact real_star_mul_imaginary _ _ (meanTransportFactor_re_zero c.val hreal k)

theorem laplacianFrequency_nonneg (k : Frequency) : 0 ≤ laplacianFrequency k := by
  unfold laplacianFrequency
  exact mul_nonneg (sq_nonneg _) (by exact_mod_cast galerkinFreqSq_nonneg k)

/-- The actual triad-free forced mode obeys a scalar energy inequality.
This can be summed over finite weighted mode sets before taking limits. -/
theorem PreterminalNSE.triad_free_mode_energy_bound
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (hν : 0 ≤ ν) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (hF : Continuous (F t))
    (htriad : ¬ HasActiveNoncollinearTriad (datumFourierCoeff (u t)))
    (k : Frequency) (i : Fin 3) :
    deriv (fun r => Complex.normSq (datumFourierCoeff (u r) k i)) t ≤
      Complex.normSq (datumFourierCoeff (u t) k i) +
        Complex.normSq (coefficientLeray k (datumFourierCoeff (F t) k) i) := by
  rw [(complex_normSq_hasDerivAt (H.projected_fourier_hasDerivAt t ht hF k i)).deriv]
  have hN := triad_free_projected_modal_transfer_zero (H.sobolevSlice t ht)
    (datumFourierCoeff_reality (u t)) (H.fourier_solenoidal t ht) htriad k i
  simpa only [neg_mul] using complex_forced_energy_bound
    (datumFourierCoeff (u t) k i)
    (coefficientLeray k (fullTransportCoefficients (H.sobolevSlice t ht) k) i)
    (coefficientLeray k (datumFourierCoeff (F t) k) i)
    (ν * laplacianFrequency k) (mul_nonneg hν (laplacianFrequency_nonneg k)) hN

end MethbokeAddon.FDSN
