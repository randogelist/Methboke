import MethbokeAddon.WeakFouriermanB.FiniteWindowCrossIdentity
import SingularClosure.CriticalRelativeEnergyTransport

/-!
Finite-window physical Leray--Hopf / smooth relative energy.

Proof bodies localize the pinned SingularClosure CriticalSmoothEnergy,
CriticalRelativeEnergy and CriticalRelativeEnergyTransport arguments. The test
velocity is smooth, periodic and solenoidal at every positive time, as required
by the weak momentum interface. The actual NSE and pressure assumptions hold
only on the specified compact interval [s,t]. The input henergy is the ordinary
physical Leray--Hopf energy inequality at s, not a relative-energy inequality.

A separate finite-front time-clamp construction supplies the global test; this
file does not assume or prove global classical NSE existence. Sources remain
outside active Material discovery pending external cached Lean verification.
No local Lean execution has been performed.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff ENNReal Topology Interval

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

private theorem finite_window_smooth_energy_pairing
    (ν : ℝ) (u : Velocity) (p : Pressure)
    (hu : CriticalPositiveSolenoidalTest u)
    (s b t : ℝ) (ht : 0 < t) (hmem : t ∈ Icc s b)
    (hp : ∀ r ∈ Icc s b, ContDiff ℝ ∞ (p r))
    (hpp : ∀ r ∈ Icc s b, SpatialPeriodic (p r))
    (hNSE : ∀ r ∈ Icc s b, ∀ x : Vec,
      timeDerivative u r x + convection (u r) x + SingularClosure.gradient (p r) x =
        ν • laplacian (u r) x) :
    physicalFieldInner (u t) (timeDerivative u t) = -ν * physicalDissipation (u t) := by
  have hus := hu.spatial_smooth ht
  have hud : Continuous (timeDerivative u t) :=
    hu.timeDerivative_continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ht)
  have hconv : Continuous (convection (u t)) := convection_continuous hus
  have hgrad : Continuous (SingularClosure.gradient (p t)) := criticalWeak_gradient_continuous _ (hp t hmem)
  have hI₁ := physicalFieldInner_integrable (u t) (timeDerivative u t) hus.continuous hud
  have hI₂ := physicalFieldInner_integrable (u t) (convection (u t)) hus.continuous hconv
  have hI₃ := physicalFieldInner_integrable (u t) (SingularClosure.gradient (p t)) hus.continuous hgrad
  have hI₁₂ : IntegrableOn (fun x =>
      inner ℝ (u t x) (timeDerivative u t x) + inner ℝ (u t x) (convection (u t) x))
      unitCube volume := hI₁.add hI₂
  have heq : timeDerivative u t + convection (u t) + SingularClosure.gradient (p t) = ν • laplacian (u t) :=
    funext (fun x => hNSE t hmem x)
  have h := congrArg (physicalFieldInner (u t)) heq
  simp only [physicalFieldInner, Pi.add_apply, inner_add_right,
    Pi.smul_apply, inner_smul_right] at h
  rw [integral_add hI₁₂ hI₃, integral_add hI₁ hI₂, integral_const_mul] at h
  rw [critical_smooth_integral_inner_convection_eq_zero
      (u t) hus (hu.periodic t ht) (hu.solenoidal t ht),
    critical_smooth_integral_inner_gradient_eq_zero (u t) (p t) hus (hp t hmem)
      (hu.periodic t ht) (hpp t hmem) (hu.solenoidal t ht),
    critical_integral_inner_laplacian_self (u t) hus (hu.periodic t ht)] at h
  change (∫ x in unitCube, inner ℝ (u t x) (timeDerivative u t x)) = _
  linarith

/-- Classical energy equality uses the equation only on the selected window.
All integrability and derivative assertions are derived from the actual test.
-/
theorem finite_window_smooth_nse_energy_identity
    (ν : ℝ) (hν : 0 < ν) (u : Velocity) (p : Pressure)
    (hu : CriticalPositiveSolenoidalTest u)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (hp : ∀ r ∈ Icc s t, ContDiff ℝ ∞ (p r))
    (hpp : ∀ r ∈ Icc s t, SpatialPeriodic (p r))
    (hNSE : ∀ r ∈ Icc s t, ∀ x : Vec,
      timeDerivative u r x + convection (u r) x + SingularClosure.gradient (p r) x =
        ν • laplacian (u r) x) :
    IntervalIntegrable (fun r => physicalDissipation (u r)) volume s t ∧
      physicalEnergy (u t) + 2 * ν * (∫ r in s..t, physicalDissipation (u r)) =
        physicalEnergy (u s) := by
  have hP : ContinuousOn (fun r => physicalFieldInner (u r) (timeDerivative u r)) (Icc s t) :=
    critical_real_cube_integral_continuousOn_Icc
      (fun r x => inner ℝ (u r x) (timeDerivative u r x))
      (hu.smooth.continuousOn.inner hu.timeDerivative_continuousOn) s t hs
  have hscaled : ContinuousOn
      (fun r => (-ν)⁻¹ * physicalFieldInner (u r) (timeDerivative u r)) (Icc s t) :=
    continuousOn_const.mul hP
  have hD : ContinuousOn (fun r => physicalDissipation (u r)) (Icc s t) := by
    apply hscaled.congr
    intro r hr
    change physicalDissipation (u r) =
      (-ν)⁻¹ * physicalFieldInner (u r) (timeDerivative u r)
    rw [finite_window_smooth_energy_pairing ν u p hu s t r (hs.trans_le hr.1) hr hp hpp hNSE]
    simp only [← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr hν.ne'), one_mul]
  have hE : ContinuousOn (fun r => physicalEnergy (u r)) (Icc s t) := by
    intro r hr
    exact (hu.physicalEnergy_hasDerivAt r (hs.trans_le hr.1)).continuousAt.continuousWithinAt
  have hDI : IntervalIntegrable (fun r => physicalDissipation (u r)) volume s t :=
    hD.intervalIntegrable_of_Icc hst
  refine ⟨hDI, ?_⟩
  have hd : ∀ r ∈ Ioo s t, HasDerivAt (fun q => physicalEnergy (u q))
      ((-2 * ν) * physicalDissipation (u r)) r := by
    intro r hr
    have h := hu.physicalEnergy_hasDerivAt r (hs.trans hr.1)
    rw [finite_window_smooth_energy_pairing ν u p hu s t r (hs.trans hr.1)
      ⟨hr.1.le, hr.2.le⟩ hp hpp hNSE] at h
    convert h using 1 <;> ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hE hd
    (hDI.const_mul (-2 * ν))
  rw [intervalIntegral.integral_const_mul] at hFTC
  linarith

/-- Derived physical relative energy, with the exact weak/classical cross term. -/
theorem finite_window_lh_smooth_relative_energy_raw
    (ν : ℝ) (hν : 0 < ν) (a₀ : CriticalPhysicalL2)
    (v u : Velocity) (G : ℝ → Vec → (Vec →L[ℝ] Vec)) (p : Pressure)
    (hv : CriticalLerayHopf ν a₀ v G)
    (hu : CriticalPositiveSolenoidalTest u)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (hp : ∀ r ∈ Icc s t, ContDiff ℝ ∞ (p r))
    (hpp : ∀ r ∈ Icc s t, SpatialPeriodic (p r))
    (hNSE : ∀ r ∈ Icc s t, ∀ x : Vec,
      timeDerivative u r x + convection (u r) x + SingularClosure.gradient (p r) x =
        ν • laplacian (u r) x)
    (henergy : physicalEnergy (v t) +
      2 * ν * (∫ r in s..t, criticalGradientEnergy (G r)) ≤ physicalEnergy (v s)) :
    IntervalIntegrable (fun r => criticalGradientEnergy (G r - fderiv ℝ (u r))) volume s t ∧
    IntervalIntegrable (fun r => criticalWeakTransport (v r) (u r) -
      physicalFieldInner (v r) (convection (u r))) volume s t ∧
    physicalEnergy (v t - u t) +
      2 * ν * (∫ r in s..t, criticalGradientEnergy (G r - fderiv ℝ (u r))) ≤
      physicalEnergy (v s - u s) - 2 * (∫ r in s..t,
        criticalWeakTransport (v r) (u r) - physicalFieldInner (v r) (convection (u r))) := by
  have ht : 0 < t := hs.trans_le hst
  have hclassical := finite_window_smooth_nse_energy_identity ν hν u p hu s t hs hst hp hpp hNSE
  have hcross := finite_window_weak_classical_cross_identity ν v u p hv.momentum hu
    s t hs hst hp hpp hNSE
  obtain ⟨hTime, hLap, hTransport⟩ := hv.momentum.test_integrable u hu s t hs hst
  have hDv : IntervalIntegrable (fun r => criticalGradientEnergy (G r)) volume s t := by
    apply (hv.dissipation_integrable t ht).mono_set
    rw [uIcc_of_le hst, uIcc_of_le ht.le]
    exact Icc_subset_Icc hs.le le_rfl
  have hN : IntervalIntegrable (fun r => criticalWeakTransport (v r) (u r) -
      physicalFieldInner (v r) (convection (u r))) volume s t := by
    apply (hcross.1.sub (hLap.const_mul (2 * ν))).congr
    intro r _
    ring
  have hcross_eq : physicalFieldInner (v t) (u t) - physicalFieldInner (v s) (u s) =
      2 * ν * (∫ r in s..t, physicalFieldInner (v r) (laplacian (u r))) +
        (∫ r in s..t, criticalWeakTransport (v r) (u r) -
          physicalFieldInner (v r) (convection (u r))) := by
    rw [hcross.2]
    calc
      _ = ∫ r in s..t,
          (2 * ν) * physicalFieldInner (v r) (laplacian (u r)) +
            (criticalWeakTransport (v r) (u r) - physicalFieldInner (v r) (convection (u r))) := by
        apply intervalIntegral.integral_congr
        intro r _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hLap.const_mul (2 * ν)) hN,
          intervalIntegral.integral_const_mul]
  have hH1 : ∀ᵐ r ∂volume.restrict (Ioc s t), CriticalPhysicalH1 (v r) (G r) :=
    ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc hs.le le_rfl) (hv.spatial_H1 t ht)
  have hdiff : (fun r => criticalGradientEnergy (G r - fderiv ℝ (u r))) =ᵐ[
      volume.restrict (uIoc s t)]
      (fun r => criticalGradientEnergy (G r) + physicalDissipation (u r) +
        2 * physicalFieldInner (v r) (laplacian (u r))) := by
    rw [uIoc_of_le hst]
    filter_upwards [hH1, ae_restrict_mem measurableSet_Ioc] with r hHr hr
    have hrpos : 0 < r := hs.trans hr.1
    have hur := hu.spatial_smooth hrpos
    have hDu : MemLp (fderiv ℝ (u r)) 2 (volume.restrict unitCube) :=
      critical_continuous_memLp_cube _ (hur.continuous_fderiv (by simp)) 2
    rw [criticalGradientEnergy_sub _ _ hHr.derivative_L2 hDu,
      criticalGradientEnergy_fderiv (u r) hur]
    have hpairs := hHr.weakGradient.inner_laplacian (u r) hur (hu.periodic r hrpos)
    change physicalFieldInner (v r) (laplacian (u r)) =
      -criticalGradientPairing (G r) (fderiv ℝ (u r)) at hpairs
    linarith
  have hDvDu : IntervalIntegrable
      (fun r => criticalGradientEnergy (G r) + physicalDissipation (u r)) volume s t :=
    hDv.add hclassical.1
  have hDI : IntervalIntegrable
      (fun r => criticalGradientEnergy (G r - fderiv ℝ (u r))) volume s t :=
    (hDvDu.add (hLap.const_mul 2)).congr_ae hdiff.symm
  have hDint : (∫ r in s..t, criticalGradientEnergy (G r - fderiv ℝ (u r))) =
      (∫ r in s..t, criticalGradientEnergy (G r)) +
        (∫ r in s..t, physicalDissipation (u r)) +
          2 * (∫ r in s..t, physicalFieldInner (v r) (laplacian (u r))) := by
    rw [intervalIntegral.integral_congr_ae_restrict hdiff]
    rw [intervalIntegral.integral_add hDvDu (hLap.const_mul 2),
      intervalIntegral.integral_add hDv hclassical.1, intervalIntegral.integral_const_mul]
  refine ⟨hDI, hN, ?_⟩
  rw [critical_physicalEnergy_sub (v t) (u t) (hv.velocity_L2 t ht.le)
      (critical_continuous_memLp_cube _ (hu.spatial_smooth ht).continuous 2),
    critical_physicalEnergy_sub (v s) (u s) (hv.velocity_L2 s hs.le)
      (critical_continuous_memLp_cube _ (hu.spatial_smooth hs).continuous 2), hDint]
  nlinarith only [henergy, hclassical.2, hcross_eq]

/-- Derived physical relative energy after genuine rough transport polarization. -/
theorem finite_window_lh_smooth_relative_energy_transport
    (ν : ℝ) (hν : 0 < ν) (a₀ : CriticalPhysicalL2)
    (v u : Velocity) (G : ℝ → Vec → (Vec →L[ℝ] Vec)) (p : Pressure)
    (hv : CriticalLerayHopf ν a₀ v G)
    (hu : CriticalPositiveSolenoidalTest u)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (hp : ∀ r ∈ Icc s t, ContDiff ℝ ∞ (p r))
    (hpp : ∀ r ∈ Icc s t, SpatialPeriodic (p r))
    (hNSE : ∀ r ∈ Icc s t, ∀ x : Vec,
      timeDerivative u r x + convection (u r) x + SingularClosure.gradient (p r) x =
        ν • laplacian (u r) x)
    (henergy : physicalEnergy (v t) +
      2 * ν * (∫ r in s..t, criticalGradientEnergy (G r)) ≤ physicalEnergy (v s)) :
    IntervalIntegrable (fun r => criticalGradientEnergy (G r - fderiv ℝ (u r))) volume s t ∧
    IntervalIntegrable (fun r => criticalRoughTransport (v r - u r)
      (G r - fderiv ℝ (u r)) (u r)) volume s t ∧
    physicalEnergy (v t - u t) +
      2 * ν * (∫ r in s..t, criticalGradientEnergy (G r - fderiv ℝ (u r))) ≤
      physicalEnergy (v s - u s) + 2 * (∫ r in s..t,
        criticalRoughTransport (v r - u r) (G r - fderiv ℝ (u r)) (u r)) := by
  have ht : 0 < t := hs.trans_le hst
  obtain ⟨hDI, hNI, hrelative⟩ := finite_window_lh_smooth_relative_energy_raw
    ν hν a₀ v u G p hv hu s t hs hst hp hpp hNSE henergy
  have hH1 : ∀ᵐ r ∂volume.restrict (Ioc s t), CriticalPhysicalH1 (v r) (G r) :=
    ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc hs.le le_rfl) (hv.spatial_H1 t ht)
  have hnonlinear :
      (fun r => criticalWeakTransport (v r) (u r) -
        physicalFieldInner (v r) (convection (u r))) =ᵐ[volume.restrict (uIoc s t)]
      (fun r => -criticalRoughTransport (v r - u r)
        (G r - fderiv ℝ (u r)) (u r)) := by
    rw [uIoc_of_le hst]
    filter_upwards [hH1, ae_restrict_mem measurableSet_Ioc] with r hHr hr
    have hrpos : 0 < r := hs.trans hr.1
    have hus := hu.spatial_smooth hrpos
    have hvL2 := hv.velocity_L2 r hrpos.le
    have hdiv := hv.momentum.gradient_annihilation r hrpos
    rw [CRITICAL_RELATIVE_NONLINEAR_IDENTITY (v r) (u r) hvL2 hdiv
      hus (hu.periodic r hrpos) (hu.solenoidal r hrpos)]
    exact CRITICAL_ROUGH_TRANSPORT_SKEW (v r - u r) (G r - fderiv ℝ (u r)) (u r)
      (hHr.sub_smooth (u r) hus (hu.periodic r hrpos))
      (critical_gradient_annihilation_sub_smooth (v r) (u r) hvL2 hdiv
        hus (hu.periodic r hrpos) (hu.solenoidal r hrpos))
      hus (hu.periodic r hrpos)
  have hRI : IntervalIntegrable (fun r => criticalRoughTransport (v r - u r)
      (G r - fderiv ℝ (u r)) (u r)) volume s t := by
    apply hNI.neg.congr_ae
    filter_upwards [hnonlinear] with r hr
    exact neg_eq_iff_eq_neg.mpr hr
  have hNint : (∫ r in s..t, criticalWeakTransport (v r) (u r) -
      physicalFieldInner (v r) (convection (u r))) =
      -(∫ r in s..t, criticalRoughTransport (v r - u r)
        (G r - fderiv ℝ (u r)) (u r)) := by
    rw [intervalIntegral.integral_congr_ae_restrict hnonlinear, intervalIntegral.integral_neg]
  refine ⟨hDI, hRI, ?_⟩
  rw [hNint] at hrelative
  nlinarith only [hrelative]

end

end MethbokeAddon.WeakFouriermanB
