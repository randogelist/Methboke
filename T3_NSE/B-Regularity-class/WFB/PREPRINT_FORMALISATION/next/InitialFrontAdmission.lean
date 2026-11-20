import MethbokeAddon.WeakFouriermanB.FiniteCapGluing
import MethbokeAddon.WeakFouriermanB.CompactCylinderSerrin
import MethbokeAddon.WeakFouriermanB.LocalFrontIdentification
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
An admitted finite initial classical pair supplies its own physical trace,
local-front interface, compact Serrin bounds and same-Leray--Hopf-path
identification. Smooth data alone are not used to manufacture this pair.

The strong initial L2 trace is proved from actual joint continuity up to zero
and dominated integration on the compact cube. It is not an admission field.
No global continuation or universal finite-cap admission is concluded here.

Prepared source only; matching external cached verification is pending.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB
open scoped ContDiff ENNReal Topology

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

/-- Spatial restriction at the time boundary still gives an ordinary smooth
spatial field, since every spatial direction remains inside the cylinder. -/
theorem initial_front_smooth_slices
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p)
    (r : ℝ) (hr : r ∈ Ico (0 : ℝ) T) : SmoothSigmaZero (u r) := by
  have hsmooth : ContDiff ℝ ∞ (u r) := by
    rw [← contDiffOn_univ]
    exact H.velocity_smooth.comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => hr)
  exact ⟨hsmooth, H.velocity_periodic r hr,
    H.divergence_free r hr, H.velocity_mean_zero r hr⟩

theorem initial_front_initial_smooth
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hT : 0 < T) : SmoothSigmaZero a := by
  simpa only [H.initial] using
    initial_front_smooth_slices ν T a u p H 0 ⟨le_rfl, hT⟩

theorem initial_front_compact_cylinder_continuous
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p)
    (τ : ℝ) (hτT : τ < T) :
    ContinuousOn (fun z : ℝ × Vec => u z.1 z.2)
      (Icc (0 : ℝ) τ ×ˢ unitCube) := by
  apply H.velocity_smooth.continuousOn.mono
  intro z hz
  exact ⟨hz.1.1, hz.1.2.trans_lt hτT⟩

/-- Dominated parameter integration works at the initial boundary as well.
The bound is extracted from the actual compact cylinder. -/
theorem initial_real_cube_integral_continuousOn_Icc
    (T : ℝ) (F : ℝ → Vec → ℝ)
    (hF : ContinuousOn (fun z : ℝ × Vec => F z.1 z.2) (initialFrontSpacetime T))
    (τ : ℝ) (hτT : τ < T) :
    ContinuousOn (fun r => ∫ x in unitCube, F r x) (Icc (0 : ℝ) τ) := by
  have hsubset : Icc (0 : ℝ) τ ×ˢ unitCube ⊆ initialFrontSpacetime T := by
    intro z hz
    exact ⟨hz.1.1, hz.1.2.trans_lt hτT⟩
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) τ)).prod isCompact_unitCube).exists_bound_of_continuousOn
      (hF.mono hsubset)
  apply continuousOn_of_dominated (μ := volume.restrict unitCube)
    (bound := fun _ : Vec => C)
  · intro r hr
    have hc : Continuous (F r) :=
      hF.comp_continuous (continuous_const.prodMk continuous_id)
        (fun _ => ⟨hr.1, hr.2.trans_lt hτT⟩)
    exact hc.aestronglyMeasurable
  · intro r hr
    filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
    exact hC (r, x) ⟨hr, hx⟩
  · exact continuous_const.continuousOn.integrableOn_compact isCompact_unitCube
  · filter_upwards with x
    exact hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hr.1, hr.2.trans_lt hτT⟩)

/-- The literal strong physical L2 trace follows from initial-cylinder
smoothness and its actual initial value. It is not separately assumed. -/
theorem initial_front_strong_initial_trace
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hT : 0 < T) :
    Tendsto (fun r => eLpNorm (u r - a) 2 (volume.restrict unitCube))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ha : SmoothSigmaZero a := initial_front_initial_smooth ν T a u p H hT
  let τ : ℝ := T / 2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have hτT : τ < T := by dsimp [τ]; linarith
  have hF : ContinuousOn
      (fun z : ℝ × Vec => ‖u z.1 z.2 - a z.2‖ ^ 2) (initialFrontSpacetime T) :=
    (H.velocity_smooth.continuousOn.sub
      (ha.smooth.continuous.comp continuous_snd).continuousOn).norm.pow 2
  have hE : ContinuousOn (fun r => physicalEnergy (u r - a)) (Icc (0 : ℝ) τ) := by
    simpa only [physicalEnergy_eq_integral_norm_sq, Pi.sub_apply] using
      initial_real_cube_integral_continuousOn_Icc T
        (fun r x => ‖u r x - a x‖ ^ 2) hF τ hτT
  have hE0 : physicalEnergy (u 0 - a) = 0 := by
    simp [H.initial, physicalEnergy_eq_integral_norm_sq]
  have hτevent : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < τ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hτ)
  have hwindow : Icc (0 : ℝ) τ ∈ 𝓝[>] (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin, hτevent] with r hr hrτ
    exact ⟨hr.le, hrτ.le⟩
  have hfilter : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc (0 : ℝ) τ] (0 : ℝ) :=
    le_inf nhdsWithin_le_nhds (le_principal_iff.mpr hwindow)
  have hEtrace : Tendsto (fun r => physicalEnergy (u r - a))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h : Tendsto (fun r => physicalEnergy (u r - a))
        (𝓝[>] (0 : ℝ)) (𝓝 (physicalEnergy (u 0 - a))) :=
      (hE 0 ⟨le_rfl, hτ.le⟩).mono_left hfilter
    simpa only [hE0] using h
  have hlimit : Tendsto
      (fun r => ENNReal.ofReal (Real.sqrt (physicalEnergy (u r - a))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hEtrace
    simpa only [Function.comp_def, Real.sqrt_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal hsqrt
  have hTevent : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < T :=
    nhdsWithin_le_nhds (Iio_mem_nhds hT)
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin, hTevent] with r hr hrT
  have hur := initial_front_smooth_slices ν T a u p H r ⟨hr.le, hrT⟩
  have hmem : MemLp (u r - a) 2 (volume.restrict unitCube) :=
    (smooth_datum_memLp hur).sub (smooth_datum_memLp ha)
  have hsq := critical_velocity_L2_toReal_sq_eq_physicalEnergy (u r - a) hmem
  have hroot : Real.sqrt (physicalEnergy (u r - a)) =
      (eLpNorm (u r - a) 2 (volume.restrict unitCube)).toReal := by
    rw [← hsq, Real.sqrt_sq ENNReal.toReal_nonneg]
  rw [hroot, ENNReal.ofReal_toReal hmem.eLpNorm_lt_top.ne]

/-- All LocalPhysicalNSEFront fields are derived from the initial classical
pair, including the previously independent strong initial trace field. -/
theorem initial_front_to_local_physical
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hν : 0 < ν) (hT : 0 < T) :
    LocalPhysicalNSEFront ν T a u p := by
  exact {
    viscosity_pos := hν
    time_pos := hT
    initial_smooth := initial_front_initial_smooth ν T a u p H hT
    initial_value := H.initial
    velocity_smooth := H.velocity_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)
    pressure_smooth := H.pressure_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)
    velocity_periodic := fun r hr => H.velocity_periodic r ⟨hr.1.le, hr.2⟩
    pressure_periodic := fun r hr => H.pressure_periodic r ⟨hr.1.le, hr.2⟩
    divergence_free := fun r hr => H.divergence_free r ⟨hr.1.le, hr.2⟩
    velocity_mean_zero := fun r hr => H.velocity_mean_zero r ⟨hr.1.le, hr.2⟩
    pressure_mean_zero := fun r hr => H.pressure_mean_zero r ⟨hr.1.le, hr.2⟩
    equation := fun r hr => H.equation r ⟨hr.1.le, hr.2⟩
    strong_initial_trace := initial_front_strong_initial_trace ν T a u p H hT
  }

/-- Compact-cylinder regularity discharges the actual Serrin premise on
every shorter interval of the admitted initial classical front. -/
theorem initial_front_compact_serrin
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hν : 0 < ν) (hT : 0 < T)
    (τ : ℝ) (hτ : 0 < τ) (hτT : τ < T) :
    MemLp (fun r => criticalSpatialNorm 6 (u r)) 4
      (volume.restrict (Ioc (0 : ℝ) τ)) :=
  local_front_compact_cylinder_serrin ν T a u p
    (initial_front_to_local_physical ν T a u p H hν hT) τ hτ hτT
    (initial_front_compact_cylinder_continuous ν T a u p H τ hτT)

/-- An admitted initial classical front agrees with any original LH path
from its same physical datum. No budget, trace or Serrin premise is added. -/
theorem initial_front_leray_hopf_identification
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (v : Velocity) (G : WeakGradientTrajectory)
    (H : InitialClassicalFront ν T a u p) (hν : 0 < ν) (hT : 0 < T)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G) :
    ∀ r ∈ Ioo (0 : ℝ) T, v r =ᵐ[volume.restrict unitCube] u r :=
  local_front_leray_hopf_identification_of_compact_serrin ν T a u p v G
    (initial_front_to_local_physical ν T a u p H hν hT) hv
    (fun τ hτ hτT => initial_front_compact_serrin ν T a u p H hν hT τ hτ hτT)

/-- Q01 constructs an original weak path, then the admitted front is
identified with that same path. Existence of the front remains explicit. -/
theorem initial_front_original_leray_hopf
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hν : 0 < ν) (hT : 0 < T) :
    ∃ (v : Velocity) (G : WeakGradientTrajectory),
      CriticalLerayHopf ν (criticalL2Representative a) v G ∧
      v 0 =ᵐ[volume.restrict unitCube] a ∧
      ∀ r ∈ Ioo (0 : ℝ) T, v r =ᵐ[volume.restrict unitCube] u r := by
  obtain ⟨v, G, hv, hinitial⟩ := smooth_datum_lerayHopf_exists ν hν a
    (initial_front_initial_smooth ν T a u p H hT)
  exact ⟨v, G, hv, hinitial,
    initial_front_leray_hopf_identification ν T a u p v G H hν hT hv⟩

end

end MethbokeAddon.WeakFouriermanB
