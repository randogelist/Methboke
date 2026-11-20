import SingularClosure.CriticalSpatialNormMeasurable
import SingularClosure.CriticalSerrinTime
import SingularClosure.CriticalSmoothEnergy
import Mathlib.Topology.Order.LeftRightNhds
import SingularClosure.CriticalLerayHopf
import SingularClosure.CriticalGradientEnergyBound
import MethbokeAddon.WeakFouriermanB.FourierBudget

/-!
Local finite-front adapter for Weak_Fourierman_B.

Merged in dependency order from LocalMeasurability, LocalEnergy,
InitialEnergyTrace and LocalFrontAdapter. Proof bodies and local sections
are preserved. The completed regularity root still requires physical
endpoint continuation and same-trajectory gluing.
Prepared for external verification; no local Lean execution.
-/

set_option autoImplicit false


/-!
Local finite-front norm measurability for Weak_Fourierman_B.
All smoothness hypotheses concern only the open cylinder 0<t<T.
No positive-time-global flow wrapper or continuation hypothesis is used.
Prepared by static source inspection only; external Lean checking is pending.
-/


open Set Filter MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology

namespace MethbokeAddon.WeakFouriermanB
open SingularClosure
noncomputable section

def localFrontSpacetime (T : ℝ) : Set (ℝ × Vec) :=
  {z | z.1 ∈ Ioo (0 : ℝ) T}

theorem localFrontSpacetime_isOpen (T : ℝ) : IsOpen (localFrontSpacetime T) :=
  isOpen_Ioo.preimage continuous_fst

/-- Joint smoothness on a finite open cylinder gives every spatial slice. -/
theorem local_spatial_slice_contDiff
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (u t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hj := hu.contDiffAt ((localFrontSpacetime_isOpen T).mem_nhds
    (show (t, x) ∈ localFrontSpacetime T from ht))
  simpa only [Function.comp_def] using
    hj.comp x (contDiff_prodMk_right t).contDiffAt

/-- The actual spatial coordinate derivative is a direction of the actual
joint Frechet derivative, at a point of the finite cylinder. -/
theorem local_coordinateDerivative_eq_joint
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (x : Vec) (j : Fin 3) :
    coordinateDerivative (u t) j x =
      fderiv ℝ (fun z : ℝ × Vec => u z.1 z.2) (t, x) (0, unitVector j) := by
  have hj : DifferentiableAt ℝ (fun z : ℝ × Vec => u z.1 z.2) (t, x) :=
    (hu.contDiffAt ((localFrontSpacetime_isOpen T).mem_nhds
      (show (t, x) ∈ localFrontSpacetime T from ht))).differentiableAt (by simp)
  have hcomp : HasFDerivAt (u t)
      ((fderiv ℝ (fun z : ℝ × Vec => u z.1 z.2) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ Vec)) x := by
    simpa only [Function.comp_def] using
      hj.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  rw [coordinateDerivative, hcomp.fderiv]
  rfl

theorem local_coordinateDerivative_continuousOn
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (j : Fin 3) :
    ContinuousOn (fun z : ℝ × Vec => coordinateDerivative (u z.1) j z.2)
      (localFrontSpacetime T) := by
  have hfd : ContinuousOn (fderiv ℝ (fun z : ℝ × Vec => u z.1 z.2))
      (localFrontSpacetime T) :=
    hu.continuousOn_fderiv_of_isOpen (localFrontSpacetime_isOpen T) (by simp)
  have happ : ContinuousOn
      (fun z : ℝ × Vec => fderiv ℝ (fun q : ℝ × Vec => u q.1 q.2) z (0, unitVector j))
      (localFrontSpacetime T) := hfd.clm_apply continuousOn_const
  apply happ.congr
  intro z hz
  exact local_coordinateDerivative_eq_joint u T hu z.1 hz z.2 j

/-- A zero extension is only a measurability device; no PDE extension is made. -/
theorem local_spatialNorm_aestronglyMeasurable
    (u : Velocity) (T : ℝ)
    (hu : ContinuousOn (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ (⊤ : ℝ≥0∞)) :
    AEStronglyMeasurable (fun t => criticalSpatialNorm p (u t))
      (volume.restrict (Ioo (0 : ℝ) T)) := by
  classical
  let F : ℝ × Vec → Vec :=
    (localFrontSpacetime T).piecewise (fun z => u z.1 z.2) (fun _ => 0)
  have hopen : MeasurableSet (localFrontSpacetime T) :=
    (localFrontSpacetime_isOpen T).measurableSet
  have hF : Measurable F :=
    hu.measurable_piecewise continuousOn_const hopen
  have hnorm : Measurable (fun t => criticalSpatialNorm p (fun x => F (t, x))) := by
    simp_rw [criticalSpatialNorm, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop]
    exact (((hF.enorm.pow_const p.toReal).lintegral_prod_right').pow_const
      (1 / p.toReal)).ennreal_toReal
  apply hnorm.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  apply congrArg (criticalSpatialNorm p)
  funext x
  change (localFrontSpacetime T).piecewise (fun z => u z.1 z.2)
    (fun _ => 0) (t, x) = u t x
  exact (localFrontSpacetime T).piecewise_eq_of_mem _ _
    (show (t, x) ∈ localFrontSpacetime T from ht)

theorem local_spatialNorm_six_aestronglyMeasurable
    (u : Velocity) (T : ℝ)
    (hu : ContinuousOn (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T)) :
    AEStronglyMeasurable (fun t => criticalSpatialNorm 6 (u t))
      (volume.restrict (Ioo (0 : ℝ) T)) :=
  local_spatialNorm_aestronglyMeasurable u T hu 6 (by norm_num) (by norm_num)

/-- Actual kinetic energy is measurable from local joint continuity alone. -/
theorem local_physicalEnergy_aestronglyMeasurable
    (u : Velocity) (T : ℝ)
    (hu : ContinuousOn (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T)) :
    AEStronglyMeasurable (fun t => physicalEnergy (u t))
      (volume.restrict (Ioo (0 : ℝ) T)) := by
  have hnorm := local_spatialNorm_aestronglyMeasurable u T hu 2
    (by norm_num) (by norm_num)
  apply (hnorm.pow 2).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  change criticalSpatialNorm 2 (u t) ^ 2 = physicalEnergy (u t)
  have hc : Continuous (u t) :=
    hu.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ht)
  exact critical_velocity_L2_toReal_sq_eq_physicalEnergy (u t)
    (critical_continuous_memLp_cube (u t) hc 2)

/-- The actual dissipation is a finite sum of the energies of coordinate
derivatives. Continuity supplies all integrability needed to exchange the sum. -/
theorem physicalDissipation_eq_sum_coordinateEnergy
    (v : Field) (hv : ContDiff ℝ ∞ v) :
    physicalDissipation v = ∑ j : Fin 3, physicalEnergy (coordinateDerivative v j) := by
  have hc (j : Fin 3) : Continuous (coordinateDerivative v j) := by
    change Continuous (fun x => fderiv ℝ v x (unitVector j))
    exact (hv.continuous_fderiv (by simp)).clm_apply continuous_const
  have hI (j : Fin 3) : IntegrableOn
      (fun x => ‖coordinateDerivative v j x‖ ^ 2) unitCube volume :=
    ((hc j).norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  unfold physicalDissipation
  simp_rw [gradientSquareDensity_eq_sum_norm_sq]
  rw [integral_finsetSum Finset.univ (fun j _ => hI j)]
  simp only [physicalEnergy_eq_integral_norm_sq]

/-- Local joint smoothness makes the actual physical dissipation measurable. -/
theorem local_physicalDissipation_aestronglyMeasurable
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T)) :
    AEStronglyMeasurable (fun t => physicalDissipation (u t))
      (volume.restrict (Ioo (0 : ℝ) T)) := by
  have henergy (j : Fin 3) :
      AEStronglyMeasurable (fun t => physicalEnergy (coordinateDerivative (u t) j))
        (volume.restrict (Ioo (0 : ℝ) T)) :=
    local_physicalEnergy_aestronglyMeasurable
      (fun t => coordinateDerivative (u t) j) T
      (local_coordinateDerivative_continuousOn u T hu j)
  have hsum012 : AEStronglyMeasurable
      (fun t =>
        (physicalEnergy (coordinateDerivative (u t) 0) +
          physicalEnergy (coordinateDerivative (u t) 1)) +
          physicalEnergy (coordinateDerivative (u t) 2))
      (volume.restrict (Ioo (0 : ℝ) T)) :=
    ((henergy 0).add (henergy 1)).add (henergy 2)
  have hsum : AEStronglyMeasurable
      (fun t => ∑ j : Fin 3, physicalEnergy (coordinateDerivative (u t) j))
      (volume.restrict (Ioo (0 : ℝ) T)) := by
    simpa only [Fin.sum_univ_three] using hsum012
  apply hsum.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact (physicalDissipation_eq_sum_coordinateEnergy (u t)
    (local_spatial_slice_contDiff u T hu t ht)).symm

end
end MethbokeAddon.WeakFouriermanB

/-!
Finite-front physical NSE energy, localized from the pinned smooth-energy
proof. No globally defined solution predicate or assumed energy inequality is
used. All PDE hypotheses are required only for 0<t<T. The initial energy is
supplied by an actual right-hand trace; the final upper bound is derived.

Prepared source only. No local Lean/Lake/kernel execution.
-/


open Set Filter MeasureTheory Metric SingularClosure
open scoped ContDiff Interval Topology

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

private theorem local_energy_mem_of_half_ball {T t r : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hr : r ∈ closedBall t (min t (T - t) / 2)) :
    r ∈ Ioo (0 : ℝ) T := by
  have hh : |r - t| ≤ min t (T - t) / 2 := by
    simpa only [Metric.mem_closedBall, Real.dist_eq] using hr
  have hleft := min_le_left t (T - t)
  have hright := min_le_right t (T - t)
  have hl := (abs_le.mp hh).1
  have hu := (abs_le.mp hh).2
  constructor <;> linarith [ht.1, ht.2]

/-- Dominated differentiation is confined to a compact neighborhood strictly
inside the finite front, rather than all positive times. -/
theorem local_hasDerivAt_real_cube_integral
    (T : ℝ) (F D : ℝ → Vec → ℝ)
    (hF : ContinuousOn (fun z : ℝ × Vec => F z.1 z.2) (localFrontSpacetime T))
    (hD : ContinuousOn (fun z : ℝ × Vec => D z.1 z.2) (localFrontSpacetime T))
    (hd : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Vec,
      HasDerivAt (fun r => F r x) (D t x) t)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => ∫ x in unitCube, F r x)
      (∫ x in unitCube, D t x) t := by
  let ρ : ℝ := min t (T - t) / 2
  have hρ : 0 < ρ := div_pos (lt_min ht.1 (sub_pos.mpr ht.2)) (by norm_num)
  have hFc (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) T) : Continuous (F r) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => hr)
  have hDc (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) T) : Continuous (D r) :=
    hD.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => hr)
  have hsubset : closedBall t ρ ×ˢ unitCube ⊆ localFrontSpacetime T := by
    intro z hz
    exact local_energy_mem_of_half_ball ht hz.1
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall t ρ).prod isCompact_unitCube).exists_bound_of_continuousOn
      (hD.mono hsubset)
  have hbound : ∀ᵐ x ∂volume.restrict unitCube,
      ∀ r ∈ closedBall t ρ, ‖D r x‖ ≤ C := by
    filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
    intro r hr
    exact hC (r, x) ⟨hr, hx⟩
  have hdiff : ∀ᵐ x ∂volume.restrict unitCube,
      ∀ r ∈ closedBall t ρ, HasDerivAt (fun q => F q x) (D r x) r :=
    Filter.Eventually.of_forall fun x r hr => hd r (local_energy_mem_of_half_ball ht hr) x
  have hmeas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (F r) (volume.restrict unitCube) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact (hFc r hr).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict unitCube) (F := F) (F' := D)
    (bound := fun _ : Vec => C) (closedBall_mem_nhds t hρ) hmeas
    ((hFc t ht).continuousOn.integrableOn_compact isCompact_unitCube)
    (hDc t ht).aestronglyMeasurable hbound
    (continuous_const.continuousOn.integrableOn_compact isCompact_unitCube) hdiff).2

theorem local_real_cube_integral_continuousOn_Icc
    (T : ℝ) (F : ℝ → Vec → ℝ)
    (hF : ContinuousOn (fun z : ℝ × Vec => F z.1 z.2) (localFrontSpacetime T))
    (s t : ℝ) (hs : 0 < s) (ht : t < T) :
    ContinuousOn (fun r => ∫ x in unitCube, F r x) (Icc s t) := by
  have hsubset : Icc s t ×ˢ unitCube ⊆ localFrontSpacetime T := by
    intro z hz
    exact ⟨hs.trans_le hz.1.1, hz.1.2.trans_lt ht⟩
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc : IsCompact (Icc s t)).prod isCompact_unitCube).exists_bound_of_continuousOn
      (hF.mono hsubset)
  apply continuousOn_of_dominated (μ := volume.restrict unitCube) (bound := fun _ : Vec => C)
  · intro r hr
    have hc : Continuous (F r) :=
      hF.comp_continuous (continuous_const.prodMk continuous_id)
        (fun _ => ⟨hs.trans_le hr.1, hr.2.trans_lt ht⟩)
    exact hc.aestronglyMeasurable
  · intro r hr
    filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
    exact hC (r, x) ⟨hr, hx⟩
  · exact continuous_const.continuousOn.integrableOn_compact isCompact_unitCube
  · filter_upwards with x
    exact hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hs.trans_le hr.1, hr.2.trans_lt ht⟩)

theorem local_timeDerivative_eq_joint
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (x : Vec) :
    timeDerivative u t x =
      fderiv ℝ (fun z : ℝ × Vec => u z.1 z.2) (t, x) (1, 0) := by
  have hj : DifferentiableAt ℝ (fun z : ℝ × Vec => u z.1 z.2) (t, x) :=
    (hu.contDiffAt ((localFrontSpacetime_isOpen T).mem_nhds
      (show (t, x) ∈ localFrontSpacetime T from ht))).differentiableAt (by simp)
  have hpath : HasDerivAt (fun r : ℝ => (r, x)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have h : HasDerivAt (fun r => u r x)
      (fderiv ℝ (fun z : ℝ × Vec => u z.1 z.2) (t, x) (1, 0)) t := by
    simpa only [Function.comp_def] using hj.hasFDerivAt.comp_hasDerivAt t hpath
  change derivWithin (fun r => u r x) (Ici (0 : ℝ)) t = _
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1), h.deriv]

theorem local_time_hasDerivAt
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (x : Vec) :
    HasDerivAt (fun r => u r x) (timeDerivative u t x) t := by
  have hj : DifferentiableAt ℝ (fun z : ℝ × Vec => u z.1 z.2) (t, x) :=
    (hu.contDiffAt ((localFrontSpacetime_isOpen T).mem_nhds
      (show (t, x) ∈ localFrontSpacetime T from ht))).differentiableAt (by simp)
  have hpath : HasDerivAt (fun r : ℝ => (r, x)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  rw [local_timeDerivative_eq_joint u T hu t ht x]
  simpa only [Function.comp_def] using hj.hasFDerivAt.comp_hasDerivAt t hpath

theorem local_timeDerivative_continuousOn
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T)) :
    ContinuousOn (fun z : ℝ × Vec => timeDerivative u z.1 z.2) (localFrontSpacetime T) := by
  have hfd : ContinuousOn (fderiv ℝ (fun z : ℝ × Vec => u z.1 z.2)) (localFrontSpacetime T) :=
    hu.continuousOn_fderiv_of_isOpen (localFrontSpacetime_isOpen T) (by simp)
  have happ : ContinuousOn
      (fun z : ℝ × Vec => fderiv ℝ (fun q : ℝ × Vec => u q.1 q.2) z (1, 0))
      (localFrontSpacetime T) := hfd.clm_apply continuousOn_const
  apply happ.congr
  intro z hz
  exact local_timeDerivative_eq_joint u T hu z.1 hz z.2

theorem local_physicalEnergy_hasDerivAt
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => physicalEnergy (u r))
      (2 * physicalFieldInner (u t) (timeDerivative u t)) t := by
  have hd := local_timeDerivative_continuousOn u T hu
  have h := local_hasDerivAt_real_cube_integral T
    (fun r x => ‖u r x‖ ^ 2) (fun r x => 2 * inner ℝ (u r x) (timeDerivative u r x))
    (hu.continuousOn.norm.pow 2) (continuousOn_const.mul (hu.continuousOn.inner hd))
    (fun r hr x => (local_time_hasDerivAt u T hu r hr x).norm_sq) t ht
  simpa only [physicalEnergy_eq_integral_norm_sq, physicalFieldInner, integral_const_mul] using h

section Classical

variable (ν T : ℝ) (u : Velocity) (p : Pressure)
variable (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
variable (hperiodic : ∀ r ∈ Ioo (0 : ℝ) T, SpatialPeriodic (u r))
variable (hsolenoidal : ∀ r ∈ Ioo (0 : ℝ) T, ∀ x : Vec, divergence (u r) x = 0)
variable (hp : ∀ r ∈ Ioo (0 : ℝ) T, ContDiff ℝ ∞ (p r))
variable (hpp : ∀ r ∈ Ioo (0 : ℝ) T, SpatialPeriodic (p r))
variable (hNSE : ∀ r ∈ Ioo (0 : ℝ) T, ∀ x : Vec,
  timeDerivative u r x + convection (u r) x + SingularClosure.gradient (p r) x =
    ν • laplacian (u r) x)

include hu hperiodic hsolenoidal hp hpp hNSE

/-- Actual physical NSE pairing at a finite-front time. -/
theorem local_smooth_energy_pairing (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    physicalFieldInner (u t) (timeDerivative u t) = -ν * physicalDissipation (u t) := by
  have hus := local_spatial_slice_contDiff u T hu t ht
  have hud : Continuous (timeDerivative u t) :=
    (local_timeDerivative_continuousOn u T hu).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ht)
  have hconv : Continuous (convection (u t)) := convection_continuous hus
  have hgrad : Continuous (SingularClosure.gradient (p t)) := criticalWeak_gradient_continuous _ (hp t ht)
  have hI₁ := physicalFieldInner_integrable (u t) (timeDerivative u t) hus.continuous hud
  have hI₂ := physicalFieldInner_integrable (u t) (convection (u t)) hus.continuous hconv
  have hI₃ := physicalFieldInner_integrable (u t) (SingularClosure.gradient (p t)) hus.continuous hgrad
  have hI₁₂ : IntegrableOn (fun x =>
      inner ℝ (u t x) (timeDerivative u t x) + inner ℝ (u t x) (convection (u t) x))
      unitCube volume := hI₁.add hI₂
  have heq : timeDerivative u t + convection (u t) + SingularClosure.gradient (p t) = ν • laplacian (u t) :=
    funext (fun x => hNSE t ht x)
  have h := congrArg (physicalFieldInner (u t)) heq
  simp only [physicalFieldInner, Pi.add_apply, inner_add_right,
    Pi.smul_apply, inner_smul_right] at h
  rw [integral_add hI₁₂ hI₃, integral_add hI₁ hI₂, integral_const_mul] at h
  rw [critical_smooth_integral_inner_convection_eq_zero
      (u t) hus (hperiodic t ht) (hsolenoidal t ht),
    critical_smooth_integral_inner_gradient_eq_zero (u t) (p t) hus (hp t ht)
      (hperiodic t ht) (hpp t ht) (hsolenoidal t ht),
    critical_integral_inner_laplacian_self (u t) hus (hperiodic t ht)] at h
  change (∫ x in unitCube, inner ℝ (u t x) (timeDerivative u t x)) = _
  linarith

theorem local_nse_energy_hasDeriv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => physicalEnergy (u r))
      ((-2 * ν) * physicalDissipation (u t)) t := by
  have h := local_physicalEnergy_hasDerivAt u T hu t ht
  rw [local_smooth_energy_pairing ν T u p hu hperiodic hsolenoidal hp hpp hNSE t ht] at h
  convert h using 1 <;> ring

theorem local_nse_energy_identity (hν : 0 < ν)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t < T) :
    IntervalIntegrable (fun r => physicalDissipation (u r)) volume s t ∧
      physicalEnergy (u t) + 2 * ν * (∫ r in s..t, physicalDissipation (u r)) =
        physicalEnergy (u s) := by
  have hP : ContinuousOn (fun r => physicalFieldInner (u r) (timeDerivative u r)) (Icc s t) :=
    local_real_cube_integral_continuousOn_Icc T
      (fun r x => inner ℝ (u r x) (timeDerivative u r x))
      (hu.continuousOn.inner (local_timeDerivative_continuousOn u T hu)) s t hs ht
  have hscaled : ContinuousOn
      (fun r => (-ν)⁻¹ * physicalFieldInner (u r) (timeDerivative u r)) (Icc s t) :=
    continuousOn_const.mul hP
  have hD : ContinuousOn (fun r => physicalDissipation (u r)) (Icc s t) := by
    apply hscaled.congr
    intro r hr
    change physicalDissipation (u r) =
      (-ν)⁻¹ * physicalFieldInner (u r) (timeDerivative u r)
    rw [local_smooth_energy_pairing ν T u p hu hperiodic hsolenoidal hp hpp hNSE r
      ⟨hs.trans_le hr.1, hr.2.trans_lt ht⟩]
    simp only [← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr hν.ne'), one_mul]
  have hE : ContinuousOn (fun r => physicalEnergy (u r)) (Icc s t) := by
    intro r hr
    exact (local_physicalEnergy_hasDerivAt u T hu r
      ⟨hs.trans_le hr.1, hr.2.trans_lt ht⟩).continuousAt.continuousWithinAt
  have hDI : IntervalIntegrable (fun r => physicalDissipation (u r)) volume s t :=
    hD.intervalIntegrable_of_Icc hst
  refine ⟨hDI, ?_⟩
  have hd : ∀ r ∈ Ioo s t, HasDerivAt (fun q => physicalEnergy (u q))
      ((-2 * ν) * physicalDissipation (u r)) r := by
    intro r hr
    exact local_nse_energy_hasDeriv ν T u p hu hperiodic hsolenoidal hp hpp hNSE r
      ⟨hs.trans hr.1, hr.2.trans ht⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hE hd
    (hDI.const_mul (-2 * ν))
  rw [intervalIntegral.integral_const_mul] at hFTC
  linarith

theorem local_nse_energy_le_earlier (hν : 0 < ν)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t < T) :
    physicalEnergy (u t) ≤ physicalEnergy (u s) := by
  obtain ⟨hDI, hidentity⟩ :=
    local_nse_energy_identity ν T u p hu hperiodic hsolenoidal hp hpp hNSE hν s t hs hst ht
  have hnonneg : 0 ≤ ∫ r in s..t, physicalDissipation (u r) := by
    apply intervalIntegral.integral_nonneg hst
    intro r hr
    exact integral_nonneg (gradientSquareDensity_nonneg (u r))
  have hterm : 0 ≤ 2 * ν * (∫ r in s..t, physicalDissipation (u r)) :=
    mul_nonneg (mul_nonneg (by norm_num) hν.le) hnonneg
  linarith

/-- The energy upper bound is derived from local NSE and the right energy
trace. It is not stored as an assumed finite-front field. -/
theorem local_nse_energy_le_initial_trace (hν : 0 < ν) (E0 : ℝ)
    (htrace : Tendsto (fun r => physicalEnergy (u r)) (𝓝[>] (0 : ℝ)) (𝓝 E0))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    physicalEnergy (u t) ≤ E0 := by
  apply ge_of_tendsto htrace
  filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
  exact local_nse_energy_le_earlier ν T u p hu hperiodic hsolenoidal hp hpp hNSE
    hν s t hs.1 hs.2.le ht.2

end Classical
end
end MethbokeAddon.WeakFouriermanB

/-!
An actual strong physical L2 trace supplies the initial kinetic-energy trace.
The convergence is along an arbitrary filter; only eventual L2 membership is
needed. The final local theorem uses the same right-hand trace as the physical
Leray--Hopf interface, without assuming an energy bound or global solution.
Prepared for external verification only. No Lean execution was performed here.
-/


open Set Filter MeasureTheory SingularClosure
open scoped Topology ENNReal ContDiff

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- The literal physical kinetic energy is the squared norm of its L2 class. -/
theorem physicalEnergy_eq_L2Representative_norm_sq
    (v : Field) (hv : MemLp v 2 (volume.restrict unitCube)) :
    physicalEnergy v = ‖criticalL2Representative v‖ ^ 2 := by
  rw [criticalL2Representative_eq v hv, Lp.norm_toLp]
  exact (critical_velocity_L2_toReal_sq_eq_physicalEnergy v hv).symm

/-- Strong physical L2 convergence passes to actual equivalence classes.
Eventual membership avoids an artificial condition outside the local window. -/
theorem L2Representative_tendsto_of_strong_trace
    {ι : Type*} (l : Filter ι) (f : ι → Field) (a : Field)
    (hf : ∀ᶠ i in l, MemLp (f i) 2 (volume.restrict unitCube))
    (ha : MemLp a 2 (volume.restrict unitCube))
    (htrace : Tendsto
      (fun i => eLpNorm (f i - a) 2 (volume.restrict unitCube)) l (𝓝 0)) :
    Tendsto (fun i => criticalL2Representative (f i)) l
      (𝓝 (criticalL2Representative a)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hr : Tendsto
      (fun i => (eLpNorm (f i - a) 2 (volume.restrict unitCube)).toReal)
      l (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal
        (by simp : (0 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))).comp htrace
  apply Filter.Tendsto.congr' _ hr
  filter_upwards [hf] with i hi
  rw [criticalL2Representative_eq (f i) hi, criticalL2Representative_eq a ha,
    dist_eq_norm, ← hi.toLp_sub ha, Lp.norm_toLp]

/-- The initial energy trace follows from genuine L2 convergence. -/
theorem physical_energy_tendsto_of_L2_trace
    {ι : Type*} (l : Filter ι) (f : ι → Field) (a : Field)
    (hf : ∀ᶠ i in l, MemLp (f i) 2 (volume.restrict unitCube))
    (ha : MemLp a 2 (volume.restrict unitCube))
    (htrace : Tendsto
      (fun i => eLpNorm (f i - a) 2 (volume.restrict unitCube)) l (𝓝 0)) :
    Tendsto (fun i => physicalEnergy (f i)) l (𝓝 (physicalEnergy a)) := by
  have hLp := L2Representative_tendsto_of_strong_trace l f a hf ha htrace
  have hsq : Tendsto (fun i => ‖criticalL2Representative (f i)‖ ^ 2) l
      (𝓝 (‖criticalL2Representative a‖ ^ 2)) := hLp.norm.pow 2
  rw [← physicalEnergy_eq_L2Representative_norm_sq a ha] at hsq
  apply Filter.Tendsto.congr' _ hsq
  filter_upwards [hf] with i hi
  exact (physicalEnergy_eq_L2Representative_norm_sq (f i) hi).symm

/-- Smooth slices on a finite open front plus the actual strong initial trace
give the energy trace needed by the localized NSE energy argument. -/
theorem local_physical_energy_trace_of_strong_L2_trace
    (u : Velocity) (a : Field) (T : ℝ) (hT : 0 < T)
    (ha : ContDiff ℝ ∞ a)
    (hu : ∀ t ∈ Ioo (0 : ℝ) T, ContDiff ℝ ∞ (u t))
    (htrace : Tendsto
      (fun t => eLpNorm (u t - a) 2 (volume.restrict unitCube))
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun t => physicalEnergy (u t)) (𝓝[>] (0 : ℝ))
      (𝓝 (physicalEnergy a)) := by
  apply physical_energy_tendsto_of_L2_trace (𝓝[>] (0 : ℝ)) u a _
    (critical_continuous_memLp_cube a ha.continuous 2) htrace
  filter_upwards [Ioo_mem_nhdsGT hT] with t ht
  exact critical_continuous_memLp_cube (u t) (hu t ht).continuous 2

end
end MethbokeAddon.WeakFouriermanB

/-!
A concrete local NSE input for Weak_Fourierman_B, before continuation.
This record describes only an existing finite front and its actual initial
L2 trace. It contains no assumed energy bound, time measurability certificate,
Serrin estimate, extension, or global regularity conclusion.

The completed root still requires physical endpoint continuation and gluing.
Prepared source only; matching external Lean checking remains pending.
-/


open Set Filter MeasureTheory SingularClosure
open scoped ContDiff ENNReal Topology

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

structure LocalPhysicalNSEFront (ν T : ℝ) (a : Field)
    (u : Velocity) (p : Pressure) : Prop where
  viscosity_pos : 0 < ν
  time_pos : 0 < T
  initial_smooth : SmoothSigmaZero a
  initial_value : u 0 = a
  velocity_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T)
  pressure_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) (localFrontSpacetime T)
  velocity_periodic : ∀ t ∈ Ioo (0 : ℝ) T, SpatialPeriodic (u t)
  pressure_periodic : ∀ t ∈ Ioo (0 : ℝ) T, SpatialPeriodic (p t)
  divergence_free : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0
  velocity_mean_zero : ∀ t ∈ Ioo (0 : ℝ) T, MeanZero (u t)
  pressure_mean_zero : ∀ t ∈ Ioo (0 : ℝ) T, PressureMeanZero (p t)
  equation : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Vec,
    timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
      ν • laplacian (u t) x
  strong_initial_trace :
    Tendsto (fun t => eLpNorm (u t - a) 2 (volume.restrict unitCube))
      (𝓝[>] (0 : ℝ)) (𝓝 0)

theorem local_front_smooth_slices
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : LocalPhysicalNSEFront ν T a u p) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    SmoothSigmaZero (u t) := by
  exact ⟨local_spatial_slice_contDiff u T H.velocity_smooth t ht,
    H.velocity_periodic t ht, H.divergence_free t ht, H.velocity_mean_zero t ht⟩

theorem local_front_pressure_slice_smooth
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : LocalPhysicalNSEFront ν T a u p) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (p t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hj := H.pressure_smooth.contDiffAt
    ((localFrontSpacetime_isOpen T).mem_nhds
      (show (t, x) ∈ localFrontSpacetime T from ht))
  simpa only [Function.comp_def] using
    hj.comp x (contDiff_prodMk_right t).contDiffAt

theorem local_front_initial_energy_trace
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : LocalPhysicalNSEFront ν T a u p) :
    Tendsto (fun t => physicalEnergy (u t)) (𝓝[>] (0 : ℝ))
      (𝓝 (physicalEnergy a)) := by
  exact local_physical_energy_trace_of_strong_L2_trace u a T H.time_pos
    H.initial_smooth.smooth
    (fun t ht => (local_front_smooth_slices ν T a u p H t ht).smooth)
    H.strong_initial_trace

theorem local_front_energy_bound
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : LocalPhysicalNSEFront ν T a u p) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    physicalEnergy (u t) ≤ physicalEnergy a := by
  exact local_nse_energy_le_initial_trace ν T u p H.velocity_smooth
    H.velocity_periodic H.divergence_free
    (fun r hr => local_front_pressure_slice_smooth ν T a u p H r hr)
    H.pressure_periodic H.equation H.viscosity_pos (physicalEnergy a)
    (local_front_initial_energy_trace ν T a u p H) t ht

/-- The current Fourier-to-Serrin bridge now consumes an actual local NSE
front and its initial L2 trace. Its auxiliary energy/measurability hypotheses
are derived here, not supplied as additional regularity assumptions. -/
theorem local_front_fourier_budget_to_serrin
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : LocalPhysicalNSEFront ν T a u p)
    (hbudget : FourierBudgetFinite (fun t => datumFourierCoeff (u t)) T) :
    MemLp (fun t => criticalSpatialNorm 6 (u t)) 4
      (volume.restrict (Ioo (0 : ℝ) T)) := by
  exact physical_fourier_budget_to_serrin u T (physicalEnergy a)
    (fun t ht => local_front_smooth_slices ν T a u p H t ht)
    (local_spatialNorm_six_aestronglyMeasurable u T H.velocity_smooth.continuousOn)
    (local_physicalDissipation_aestronglyMeasurable u T H.velocity_smooth)
    (local_physicalEnergy_aestronglyMeasurable u T H.velocity_smooth.continuousOn)
    (fun t ht => local_front_energy_bound ν T a u p H t ht) hbudget

end
end MethbokeAddon.WeakFouriermanB

set_option pp.fullNames true

#check MethbokeAddon.WeakFouriermanB.localFrontSpacetime_isOpen
#print axioms MethbokeAddon.WeakFouriermanB.localFrontSpacetime_isOpen
#check MethbokeAddon.WeakFouriermanB.local_spatial_slice_contDiff
#print axioms MethbokeAddon.WeakFouriermanB.local_spatial_slice_contDiff
#check MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_eq_joint
#print axioms MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_eq_joint
#check MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_continuousOn
#print axioms MethbokeAddon.WeakFouriermanB.local_coordinateDerivative_continuousOn
#check MethbokeAddon.WeakFouriermanB.local_spatialNorm_aestronglyMeasurable
#print axioms MethbokeAddon.WeakFouriermanB.local_spatialNorm_aestronglyMeasurable
#check MethbokeAddon.WeakFouriermanB.local_spatialNorm_six_aestronglyMeasurable
#print axioms MethbokeAddon.WeakFouriermanB.local_spatialNorm_six_aestronglyMeasurable
#check MethbokeAddon.WeakFouriermanB.local_physicalEnergy_aestronglyMeasurable
#print axioms MethbokeAddon.WeakFouriermanB.local_physicalEnergy_aestronglyMeasurable
#check MethbokeAddon.WeakFouriermanB.physicalDissipation_eq_sum_coordinateEnergy
#print axioms MethbokeAddon.WeakFouriermanB.physicalDissipation_eq_sum_coordinateEnergy
#check MethbokeAddon.WeakFouriermanB.local_physicalDissipation_aestronglyMeasurable
#print axioms MethbokeAddon.WeakFouriermanB.local_physicalDissipation_aestronglyMeasurable
#check MethbokeAddon.WeakFouriermanB.local_hasDerivAt_real_cube_integral
#print axioms MethbokeAddon.WeakFouriermanB.local_hasDerivAt_real_cube_integral
#check MethbokeAddon.WeakFouriermanB.local_real_cube_integral_continuousOn_Icc
#print axioms MethbokeAddon.WeakFouriermanB.local_real_cube_integral_continuousOn_Icc
#check MethbokeAddon.WeakFouriermanB.local_timeDerivative_eq_joint
#print axioms MethbokeAddon.WeakFouriermanB.local_timeDerivative_eq_joint
#check MethbokeAddon.WeakFouriermanB.local_time_hasDerivAt
#print axioms MethbokeAddon.WeakFouriermanB.local_time_hasDerivAt
#check MethbokeAddon.WeakFouriermanB.local_timeDerivative_continuousOn
#print axioms MethbokeAddon.WeakFouriermanB.local_timeDerivative_continuousOn
#check MethbokeAddon.WeakFouriermanB.local_physicalEnergy_hasDerivAt
#print axioms MethbokeAddon.WeakFouriermanB.local_physicalEnergy_hasDerivAt
#check MethbokeAddon.WeakFouriermanB.local_smooth_energy_pairing
#print axioms MethbokeAddon.WeakFouriermanB.local_smooth_energy_pairing
#check MethbokeAddon.WeakFouriermanB.local_nse_energy_hasDeriv
#print axioms MethbokeAddon.WeakFouriermanB.local_nse_energy_hasDeriv
#check MethbokeAddon.WeakFouriermanB.local_nse_energy_identity
#print axioms MethbokeAddon.WeakFouriermanB.local_nse_energy_identity
#check MethbokeAddon.WeakFouriermanB.local_nse_energy_le_earlier
#print axioms MethbokeAddon.WeakFouriermanB.local_nse_energy_le_earlier
#check MethbokeAddon.WeakFouriermanB.local_nse_energy_le_initial_trace
#print axioms MethbokeAddon.WeakFouriermanB.local_nse_energy_le_initial_trace
#check MethbokeAddon.WeakFouriermanB.physicalEnergy_eq_L2Representative_norm_sq
#print axioms MethbokeAddon.WeakFouriermanB.physicalEnergy_eq_L2Representative_norm_sq
#check MethbokeAddon.WeakFouriermanB.L2Representative_tendsto_of_strong_trace
#print axioms MethbokeAddon.WeakFouriermanB.L2Representative_tendsto_of_strong_trace
#check MethbokeAddon.WeakFouriermanB.physical_energy_tendsto_of_L2_trace
#print axioms MethbokeAddon.WeakFouriermanB.physical_energy_tendsto_of_L2_trace
#check MethbokeAddon.WeakFouriermanB.local_physical_energy_trace_of_strong_L2_trace
#print axioms MethbokeAddon.WeakFouriermanB.local_physical_energy_trace_of_strong_L2_trace
#check MethbokeAddon.WeakFouriermanB.local_front_smooth_slices
#print axioms MethbokeAddon.WeakFouriermanB.local_front_smooth_slices
#check MethbokeAddon.WeakFouriermanB.local_front_pressure_slice_smooth
#print axioms MethbokeAddon.WeakFouriermanB.local_front_pressure_slice_smooth
#check MethbokeAddon.WeakFouriermanB.local_front_initial_energy_trace
#print axioms MethbokeAddon.WeakFouriermanB.local_front_initial_energy_trace
#check MethbokeAddon.WeakFouriermanB.local_front_energy_bound
#print axioms MethbokeAddon.WeakFouriermanB.local_front_energy_bound
#check MethbokeAddon.WeakFouriermanB.local_front_fourier_budget_to_serrin
#print axioms MethbokeAddon.WeakFouriermanB.local_front_fourier_budget_to_serrin
