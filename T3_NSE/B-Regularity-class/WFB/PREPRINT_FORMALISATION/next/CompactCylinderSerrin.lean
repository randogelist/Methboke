import MethbokeAddon.WeakFouriermanB.LocalFront
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
Compact-cylinder continuity supplies a genuine finite-front Serrin bound.

The physical velocity is bounded on the actual compact time-space cylinder.
Its L6 slice norm is compared with a constant function on the finite cube;
the upper eLpNorm is proved finite before passing to real values. Actual
time measurability and finite time measure then give L4 membership.

The continuity premise is a direct regularity property, supplied by an
admitted analytic cylinder. It is neither an assumed Serrin bound nor a
global continuation certificate. External cached verification is pending.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory SingularClosure
open scoped ContDiff ENNReal Topology

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

theorem compact_cylinder_velocity_bound (u : Velocity) (τ : ℝ)
    (hcont : ContinuousOn (fun z : ℝ × Vec => u z.1 z.2)
      (Icc (0 : ℝ) τ ×ˢ unitCube)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ r ∈ Icc (0 : ℝ) τ, ∀ x ∈ unitCube, ‖u r x‖ ≤ M := by
  obtain ⟨M, hM⟩ :=
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) τ)).prod isCompact_unitCube).exists_bound_of_continuousOn
      hcont
  refine ⟨max M 0, le_max_right M 0, ?_⟩
  intro r hr x hx
  exact (hM (r, x) ⟨hr, hx⟩).trans (le_max_left M 0)

/-- The comparison constant is the literal spatial L6 norm of the constant
scalar function. Its finiteness is proved from the cube's finite measure. -/
theorem spatialNorm_six_le_constant_of_cube_bound (v : Field) (M : ℝ)
    (hbound : ∀ x ∈ unitCube, ‖v x‖ ≤ M) :
    criticalSpatialNorm 6 v ≤ criticalSpatialNorm 6 (fun _ : Vec => M) := by
  haveI : IsFiniteMeasure (volume.restrict unitCube) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      isCompact_unitCube.measure_lt_top (μ := volume)⟩
  have hconst : MemLp (fun _ : Vec => M) 6 (volume.restrict unitCube) :=
    memLp_const M
  have hae : ∀ᵐ x ∂volume.restrict unitCube, ‖v x‖ ≤ M := by
    filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
    exact hbound x hx
  have hnorm : eLpNorm v 6 (volume.restrict unitCube) ≤
      eLpNorm (fun _ : Vec => M) 6 (volume.restrict unitCube) :=
    eLpNorm_mono_ae_real hae
  exact ENNReal.toReal_mono hconst.eLpNorm_lt_top.ne hnorm

theorem compact_cylinder_spatialNorm_six_bound (u : Velocity) (τ : ℝ)
    (hcont : ContinuousOn (fun z : ℝ × Vec => u z.1 z.2)
      (Icc (0 : ℝ) τ ×ˢ unitCube)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ r ∈ Icc (0 : ℝ) τ, criticalSpatialNorm 6 (u r) ≤ C := by
  obtain ⟨M, hM0, hM⟩ := compact_cylinder_velocity_bound u τ hcont
  refine ⟨criticalSpatialNorm 6 (fun _ : Vec => M),
    criticalSpatialNorm_nonneg 6 _, ?_⟩
  intro r hr
  exact spatialNorm_six_le_constant_of_cube_bound (u r) M (hM r hr)

/-- An actual finite physical NSE front, continuous on the closed shorter
cylinder including its initial trace, has the genuine L4-time/L6-space bound.
No squared Fourier budget or globally smooth trajectory is assumed. -/
theorem local_front_compact_cylinder_serrin
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : LocalPhysicalNSEFront ν T a u p)
    (τ : ℝ) (hτ : 0 < τ) (hτT : τ < T)
    (hcont : ContinuousOn (fun z : ℝ × Vec => u z.1 z.2)
      (Icc (0 : ℝ) τ ×ˢ unitCube)) :
    MemLp (fun r => criticalSpatialNorm 6 (u r)) 4
      (volume.restrict (Ioc (0 : ℝ) τ)) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) τ)) :=
    ⟨by simp only [Measure.restrict_apply_univ, Real.volume_Ioc]; finiteness⟩
  have hsub : Ioc (0 : ℝ) τ ⊆ Ioo (0 : ℝ) T := by
    intro r hr
    exact ⟨hr.1, hr.2.trans_lt hτT⟩
  have hmeas : AEStronglyMeasurable (fun r => criticalSpatialNorm 6 (u r))
      (volume.restrict (Ioc (0 : ℝ) τ)) := by
    have hfull := local_spatialNorm_six_aestronglyMeasurable u T
      H.velocity_smooth.continuousOn
    exact hfull.mono_measure (Measure.restrict_mono_set volume hsub)
  obtain ⟨C, hC0, hC⟩ := compact_cylinder_spatialNorm_six_bound u τ hcont
  apply MemLp.of_bound hmeas C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [Real.norm_of_nonneg (criticalSpatialNorm_nonneg 6 (u r))]
  exact hC r ⟨hr.1.le, hr.2⟩

end

end MethbokeAddon.WeakFouriermanB
