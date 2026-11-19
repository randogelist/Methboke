import MethbokeAddon.WeakFouriermanB.FiniteCapGluing
import SingularClosure.SobolevCoefficientCalculus
import SingularClosure.SobolevScaleTimeSmooth
import SingularClosure.SobolevSpacetimeSmooth
import SingularClosure.SobolevPressure
import SingularClosure.PhysicalNSEIdentity
import SingularClosure.PeriodicFourierInjective
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
Finite-window calculus and physical recovery for an actual compatible Sobolev
scale. The record below contains the literal untruncated Fourier equation and
spectral invariants; it contains no physical solution or existence conclusion.
All calculus includes the initial endpoint. Existence of the Sobolev scale is a
separate Galerkin-limit construction. Prepared source; external checking pending.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped ContDiff Topology Interval

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

/-- Modal integral identities and a continuous Sobolev RHS give the actual
Hilbert-valued derivative throughout a closed finite interval, including zero.
-/
theorem local_sobolev_hasDerivWithinAt_of_coefficient_integral
    (s : ℕ) (T : ℝ) (hT : 0 ≤ T) (u r : ℝ → TorusSobolev s)
    (hr : ContinuousOn r (Icc (0 : ℝ) T))
    (hcoeff : ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Frequency, ∀ i : Fin 3,
      (u t).val k i = (u 0).val k i + ∫ z in (0 : ℝ)..t, (r z).val k i)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt u (r t) (Icc (0 : ℝ) T) t := by
  let r' : ℝ → TorusSobolev s := fun z => r (min (max z 0) T)
  have hr' : Continuous r' :=
    hr.comp_continuous ((continuous_id.max continuous_const).min continuous_const)
      (fun z => ⟨le_min (le_max_right z 0) hT, min_le_right _ _⟩)
  have hidentity (z : ℝ) (hz : z ∈ Icc (0 : ℝ) T) :
      u z = u 0 + ∫ y in (0 : ℝ)..z, r' y := by
    have hri : IntervalIntegrable r volume 0 z :=
      (hr.mono (fun y hy => ⟨hy.1, hy.2.trans hz.2⟩)).intervalIntegrable_of_Icc hz.1
    rw [torusSobolev_integral_eq_of_coefficient_integral s u r z hri (hcoeff z hz)]
    congr 1
    apply intervalIntegral.integral_congr
    intro y hy
    have hm : y ∈ Icc (0 : ℝ) z := by simpa only [uIcc_of_le hz.1] using hy
    simp only [r', max_eq_left hm.1, min_eq_left (hm.2.trans hz.2)]
  have hd : HasDerivWithinAt
      (fun z => u 0 + ∫ y in (0 : ℝ)..z, r' y) (r' t) (Icc (0 : ℝ) T) t :=
    ((hr'.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (u 0)).hasDerivWithinAt
  have hu := hd.congr_of_mem (fun z hz => hidentity z hz) ht
  simpa only [r', max_eq_left ht.1, min_eq_left ht.2] using hu

/-- Simultaneous time differentiation on a finite Sobolev scale. -/
theorem local_sobolevScale_contDiffOn_nat
    (T : ℝ) (hT : 0 < T)
    (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (F : ∀ m : ℕ, TorusSobolev (m + 2) → TorusSobolev m)
    (hU : ∀ m : ℕ, ContinuousOn (U m) (Icc (0 : ℝ) T))
    (hF : ∀ m : ℕ, ContDiff ℝ ∞ (F m))
    (hderiv : ∀ (m : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (U m) (F m (U (m + 2) t)) (Icc (0 : ℝ) T) t)
    (n m : ℕ) : ContDiffOn ℝ n (U m) (Icc (0 : ℝ) T) := by
  induction n generalizing m with
  | zero => exact contDiffOn_zero.mpr (hU m)
  | succ n ih =>
      change ContDiffOn ℝ ((n : ℕ∞ω) + 1) (U m) (Icc (0 : ℝ) T)
      apply (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)).mpr
      refine ⟨fun t ht => (hderiv m t ht).differentiableWithinAt, by simp, ?_⟩
      have hcomp : ContDiffOn ℝ n (fun t => F m (U (m + 2) t)) (Icc (0 : ℝ) T) :=
        ((contDiff_infty.mp (hF m)) n).fun_comp_contDiffOn (ih (m + 2))
      apply hcomp.congr
      intro t ht
      exact (hderiv m t ht).derivWithin ((uniqueDiffOn_Icc hT) t ht)

theorem local_sobolev_scale_time_smooth
    (T : ℝ) (hT : 0 < T)
    (U : ∀ m : ℕ, ℝ → TorusSobolev m)
    (F : ∀ m : ℕ, TorusSobolev (m + 2) → TorusSobolev m)
    (hU : ∀ m : ℕ, ContinuousOn (U m) (Icc (0 : ℝ) T))
    (hF : ∀ m : ℕ, ContDiff ℝ ∞ (F m))
    (hderiv : ∀ (m : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (U m) (F m (U (m + 2) t)) (Icc (0 : ℝ) T) t) :
    ∀ m : ℕ, ContDiffOn ℝ ∞ (U m) (Icc (0 : ℝ) T) := by
  intro m
  apply contDiffOn_infty.mpr
  intro n
  exact local_sobolevScale_contDiffOn_nat T hT U F hU hF hderiv n m

theorem local_sobolev_curves_joint_spacetime_smooth
    (T : ℝ) (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (hU : ∀ s : ℕ, ContDiffOn ℝ ∞ (U s) (Icc (0 : ℝ) T))
    (hcoeff : ∀ (s : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      (U s t).val = (U 0 t).val) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => smoothFourierSynthesis (U 0 z.1).val z.2)
      (initialFrontSpacetime T) := by
  apply contDiffOn_infty.mpr
  intro n
  have hE : ContDiffOn ℝ n (fun z : ℝ × Vec => sobolevPhysicalEvaluation n z.2)
      (initialFrontSpacetime T) :=
    ((sobolevPhysicalEvaluation_contDiff n).comp contDiff_snd).contDiffOn
  have htime : ContDiffOn ℝ n (fun z : ℝ × Vec => U (n + 4) z.1)
      (initialFrontSpacetime T) :=
    ((contDiffOn_infty.mp (hU (n + 4))) n).comp contDiff_fst.contDiffOn
      (fun z hz => ⟨hz.1, hz.2.le⟩)
  have h : ContDiffOn ℝ n
      (fun z : ℝ × Vec => smoothFourierSynthesis (U (n + 4) z.1).val z.2)
      (initialFrontSpacetime T) := by
    simpa only [sobolevPhysicalEvaluation_apply] using hE.clm_apply htime
  apply h.congr
  intro z hz
  exact congrArg (fun c : FourierCoeff => smoothFourierSynthesis c z.2)
    (hcoeff (n + 4) z.1 ⟨hz.1, hz.2.le⟩).symm

theorem local_sobolevTransportPressureCurve_contDiffOn
    (T : ℝ) (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (hU : ∀ s : ℕ, ContDiffOn ℝ ∞ (U s) (Icc (0 : ℝ) T)) (s : ℕ) :
    ContDiffOn ℝ ∞ (sobolevTransportPressureCurve U s) (Icc (0 : ℝ) T) := by
  have hprod : ContDiffOn ℝ ∞
      (fun t => sobolevDivergenceProduct s (U (s + 2) t) (U (s + 2) t))
      (Icc (0 : ℝ) T) :=
    (sobolevDivergenceProduct_diagonal_contDiff s).fun_comp_contDiffOn (hU (s + 2))
  exact ((torusSobolevPressure s).restrictScalars ℝ).contDiff.fun_comp_contDiffOn hprod

theorem local_sobolevTransportPressureCurve_coeff
    (T : ℝ) (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (hcoeff : ∀ (s : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      (U s t).val = (U 0 t).val)
    (s : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    (sobolevTransportPressureCurve U s t).val =
      pressureVectorCoeff (fullTransportCoefficients (U 0 t)) := by
  have hlower : torusSobolevLower 0 (s + 2) (Nat.zero_le _) (U (s + 2) t) = U 0 t := by
    apply Subtype.ext
    simpa only [torusSobolevLower_coeff] using hcoeff (s + 2) t ht
  rw [sobolevTransportPressureCurve, torusSobolevPressure_coeff, sobolevDivergenceProduct_coeff]
  apply congrArg pressureVectorCoeff
  funext k i
  unfold sobolevDivergenceProductCoeff fullTransportCoefficients
  simp only [hlower]

theorem local_sobolev_pressure_joint_smooth
    (T : ℝ) (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (hU : ∀ s : ℕ, ContDiffOn ℝ ∞ (U s) (Icc (0 : ℝ) T))
    (hcoeff : ∀ (s : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      (U s t).val = (U 0 t).val) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => fullTransportPressure (U 0 z.1) z.2)
      (initialFrontSpacetime T) := by
  have hP : ∀ (s : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T →
      (sobolevTransportPressureCurve U s t).val =
        (sobolevTransportPressureCurve U 0 t).val := by
    intro s t ht
    rw [local_sobolevTransportPressureCurve_coeff T U hcoeff s t ht,
      local_sobolevTransportPressureCurve_coeff T U hcoeff 0 t ht]
  have hjoint := local_sobolev_curves_joint_spacetime_smooth T
    (sobolevTransportPressureCurve U) (local_sobolevTransportPressureCurve_contDiffOn T U hU) hP
  have hscalar := (EuclideanSpace.proj (0 : Fin 3) : Vec →L[ℝ] ℝ).contDiff.fun_comp_contDiffOn hjoint
  apply hscalar.congr
  intro z hz
  change fullTransportPressure (U 0 z.1) z.2 =
    smoothFourierSynthesis (sobolevTransportPressureCurve U 0 z.1).val z.2 0
  rw [local_sobolevTransportPressureCurve_coeff T U hcoeff 0 z.1 ⟨hz.1, hz.2.le⟩,
    smoothFourierSynthesis_pressureVector_first]
  rfl

/-- Compatible actual Sobolev trajectories solving the untruncated Fourier NSE
on a fixed closed interval. No physical realization is assumed in this record.
-/
structure LocalSobolevFlow (ν T : ℝ) where
  state : ∀ r : ℕ, ℝ → TorusSobolev r
  continuous : ∀ r : ℕ, ContinuousOn (state r) (Icc (0 : ℝ) T)
  coeff : ∀ (r : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T →
    (state r t).val = (state 0 t).val
  derivative : ∀ (r : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) T →
    HasDerivWithinAt (state r) (fourierSobolevRhs ν r (state (r + 2) t))
      (Icc (0 : ℝ) T) t
  reality : ∀ t ∈ Icc (0 : ℝ) T, SpectralReality (state 0 t).val
  solenoidal : ∀ t ∈ Icc (0 : ℝ) T, SpectralSolenoidal (state 0 t).val
  mean_zero : ∀ t ∈ Icc (0 : ℝ) T, SpectralMeanZero (state 0 t).val

def LocalSobolevFlow.velocity {ν T : ℝ} (L : LocalSobolevFlow ν T) : Velocity :=
  fun t => smoothFourierSynthesis (L.state 0 t).val

def LocalSobolevFlow.pressure {ν T : ℝ} (L : LocalSobolevFlow ν T) : Pressure :=
  fun t => fullTransportPressure (L.state 0 t)

theorem LocalSobolevFlow.state_all_mem
    {ν T : ℝ} (L : LocalSobolevFlow ν T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (s : ℕ) :
    Memℓp (sobolevWeightedCoeff s (L.state 0 t).val) 2 := by
  rw [← L.coeff s t ht]
  exact (L.state s t).property

theorem LocalSobolevFlow.rhs_coeff
    {ν T : ℝ} (L : LocalSobolevFlow ν T) (r : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    (fourierSobolevRhs ν r (L.state (r + 2) t)).val = fullFourierRhs ν (L.state 0 t) := by
  have hlower : torusSobolevLower 0 (r + 2) (Nat.zero_le _) (L.state (r + 2) t) =
      L.state 0 t := by
    apply Subtype.ext
    rw [torusSobolevLower_coeff]
    exact L.coeff (r + 2) t ht
  rw [fourierSobolevRhs_coefficient_eq_fullRhs, hlower]

theorem LocalSobolevFlow.time_smooth
    {ν T : ℝ} (L : LocalSobolevFlow ν T) (hT : 0 < T) :
    ∀ r : ℕ, ContDiffOn ℝ ∞ (L.state r) (Icc (0 : ℝ) T) :=
  local_sobolev_scale_time_smooth T hT L.state (fourierSobolevRhs ν)
    L.continuous (fourierSobolevRhs_contDiff ν) L.derivative

theorem LocalSobolevFlow.velocity_spacetime_smooth
    {ν T : ℝ} (L : LocalSobolevFlow ν T) (hT : 0 < T) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => L.velocity z.1 z.2) (initialFrontSpacetime T) :=
  local_sobolev_curves_joint_spacetime_smooth T L.state (L.time_smooth hT) L.coeff

theorem LocalSobolevFlow.pressure_spacetime_smooth
    {ν T : ℝ} (L : LocalSobolevFlow ν T) (hT : 0 < T) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => L.pressure z.1 z.2) (initialFrontSpacetime T) :=
  local_sobolev_pressure_joint_smooth T L.state (L.time_smooth hT) L.coeff

theorem LocalSobolevFlow.velocity_timeDerivative
    {ν T : ℝ} (L : LocalSobolevFlow ν T) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    timeDerivative L.velocity t = smoothFourierSynthesis (fullFourierRhs ν (L.state 0 t)) := by
  funext x
  have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
  have hd := (sobolevPhysicalEvaluation4 x).hasFDerivAt.comp_hasDerivWithinAt t
    (L.derivative 4 t ht')
  have h4 : HasDerivWithinAt
      (fun z => smoothFourierSynthesis (L.state 4 z).val x)
      (smoothFourierSynthesis (fourierSobolevRhs ν 4 (L.state 6 t)).val x)
      (Icc (0 : ℝ) T) t := by
    simpa only [Function.comp_def, sobolevPhysicalEvaluation4,
      sobolevPhysicalEvaluation_apply] using! hd
  have h0 : HasDerivWithinAt (fun z => L.velocity z x)
      (smoothFourierSynthesis (fullFourierRhs ν (L.state 0 t)) x)
      (Icc (0 : ℝ) T) t := by
    rw [L.rhs_coeff 4 t ht'] at h4
    apply h4.congr_of_mem _ ht'
    intro z hz
    exact congrArg (fun c : FourierCoeff => smoothFourierSynthesis c x) (L.coeff 4 z hz).symm
  have hlocal : Icc (0 : ℝ) T ∈ 𝓝[Ici (0 : ℝ)] t := by
    filter_upwards [self_mem_nhdsWithin,
      (Iio_mem_nhds ht.2).filter_mono nhdsWithin_le_nhds] with z hz hzT
    exact ⟨hz, hzT.le⟩
  exact (h0.mono_of_mem_nhdsWithin hlocal).derivWithin ((uniqueDiffOn_Ici 0) t ht.1)

theorem LocalSobolevFlow.physical_equation
    {ν T : ℝ} (L : LocalSobolevFlow ν T) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) (x : Vec) :
    timeDerivative L.velocity t x + convection (L.velocity t) x +
      SingularClosure.gradient (L.pressure t) x = ν • laplacian (L.velocity t) x := by
  have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
  have hr (s : ℕ) : Memℓp (sobolevWeightedCoeff s (fullFourierRhs ν (L.state 0 t))) 2 := by
    rw [← L.rhs_coeff s t ht']
    exact (fourierSobolevRhs ν s (L.state (s + 2) t)).property
  rw [L.velocity_timeDerivative t ht]
  exact PHYSICAL_NSE_OF_FULL_FOURIER_RHS ν (L.state 0 t) (L.state_all_mem t ht')
    (L.reality t ht') (L.solenoidal t ht') hr x

theorem LocalSobolevFlow.velocity_smoothSigmaZero
    {ν T : ℝ} (L : LocalSobolevFlow ν T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    SmoothSigmaZero (L.velocity t) :=
  smoothFourierSynthesis_smoothSigmaZero (L.state 0 t).val (L.state_all_mem t ht)
    (L.mean_zero t ht) (L.solenoidal t ht)

theorem LocalSobolevFlow.initial_eq
    {ν T : ℝ} (L : LocalSobolevFlow ν T) (hT : 0 ≤ T)
    (a : Field) (ha : SmoothSigmaZero a)
    (hinitial : (L.state 0 0).val = datumFourierCoeff a) : L.velocity 0 = a := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hv := L.velocity_smoothSigmaZero 0 h0
  apply datumFourierCoeff_injective_continuous_periodic (L.velocity 0) a
    hv.smooth.continuous ha.smooth.continuous hv.periodic ha.periodic
  change datumFourierCoeff (smoothFourierSynthesis (L.state 0 0).val) = datumFourierCoeff a
  rw [datumFourierCoeff_smoothFourierSynthesis _
    (ALL_SOBOLEV_IMP_RAPID_SCALAR _ (L.state_all_mem 0 h0)) (L.reality 0 h0)]
  exact hinitial

/-- An actual local Sobolev flow with the literal initial coefficients gives
the finite classical front, including its normalized pressure and time zero.
-/
theorem LocalSobolevFlow.initialClassicalFront
    {ν T : ℝ} (L : LocalSobolevFlow ν T) (hT : 0 < T)
    (a : Field) (ha : SmoothSigmaZero a)
    (hinitial : (L.state 0 0).val = datumFourierCoeff a) :
    InitialClassicalFront ν T a L.velocity L.pressure := by
  refine {
    velocity_smooth := L.velocity_spacetime_smooth hT
    pressure_smooth := L.pressure_spacetime_smooth hT
    velocity_periodic := fun t ht => (L.velocity_smoothSigmaZero t ⟨ht.1, ht.2.le⟩).periodic
    pressure_periodic := fun t _ => fullTransportPressure_periodic (L.state 0 t)
    divergence_free := fun t ht => (L.velocity_smoothSigmaZero t ⟨ht.1, ht.2.le⟩).divergence_free
    equation := L.physical_equation
    initial := L.initial_eq hT.le a ha hinitial
    velocity_mean_zero := fun t ht => (L.velocity_smoothSigmaZero t ⟨ht.1, ht.2.le⟩).mean_zero
    pressure_mean_zero := ?_
  }
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
  exact fullTransportPressure_meanZero (L.state 0 t) (L.state_all_mem t ht')
    (L.reality t ht') (L.solenoidal t ht')

end

end MethbokeAddon.WeakFouriermanB
