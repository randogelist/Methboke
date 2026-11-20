import MethbokeAddon.WeakFouriermanB.FiniteCapGluing
import MethbokeAddon.WeakFouriermanB.PressureUniqueness

/-!
# Actual finite-cap/tail agreement through the same physical weak path

SOURCE_PREPARED_ONLY. Matching external cached compilation and theorem-level
audits are pending. The intended module name is
`MethbokeAddon.WeakFouriermanB.FiniteCapOverlap`; this source is staged outside
active Material discovery and imports the other staged candidates by their
intended module names. No local Lean execution occurred.

Inputs are the literal `InitialClassicalFront`, original `ClassicalTail`, and
almost-everywhere agreement of both velocity representatives with one common
path at every time in the open overlap. The common path need not be continuous:
continuity and periodicity come from the two classical pairs. Fourier
injectivity upgrades spatial almost-everywhere equality to pointwise equality.
Local derivative congruence, the actual NSE equations and actual zero pressure
means then force pointwise pressure equality.

This lemma does not supply the weak/strong comparison needed to establish the
front's agreement premise. It also does not assert that the overlap is nonempty;
the gluing theorem separately requires `δ < T`. No equality or continuation
conclusion is put inside a new certificate field.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB
open scoped ContDiff Topology

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- Joint smoothness on an open time cylinder gives a genuinely smooth spatial
velocity slice. This is a restriction/composition fact, not an existence claim.
-/
theorem velocity_slice_contDiff_on_open_time_set
    {u : Velocity} {I : Set ℝ} (hI : IsOpen I)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      {z : ℝ × Vec | z.1 ∈ I}) {t : ℝ} (ht : t ∈ I) :
    ContDiff ℝ ∞ (u t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hopen : IsOpen {z : ℝ × Vec | z.1 ∈ I} := hI.preimage continuous_fst
  have hj := hu.contDiffAt (hopen.mem_nhds
    (show (t, x) ∈ {z : ℝ × Vec | z.1 ∈ I} from ht))
  simpa only [Function.comp_def] using
    hj.comp x (contDiff_prodMk_right t).contDiffAt

/-- Same-path almost-everywhere agreement yields actual pointwise velocity
and normalized-pressure agreement throughout the open finite-cap/tail overlap.

The common-path premises use the same orientation as `HasSmoothTail`:
`w r =ᵐ classical_velocity r`. They are required at every overlap time, not
merely almost every time. No weak representative is differentiated here.
-/
theorem finite_cap_tail_overlap_of_same_path_ae
    (ν T δ : ℝ) (a : Field) (u v w : Velocity) (p q : Pressure)
    (H : InitialClassicalFront ν T a u p) (K : ClassicalTail ν δ v q)
    (hδ0 : 0 ≤ δ)
    (hfront_agrees : ∀ r ∈ Ioo δ T, w r =ᵐ[volume.restrict unitCube] u r)
    (htail_agrees : ∀ r ∈ Ioo δ T, w r =ᵐ[volume.restrict unitCube] v r) :
    (∀ r ∈ Ioo δ T, u r = v r) ∧ (∀ r ∈ Ioo δ T, p r = q r) := by
  have hfront_time (r : ℝ) (hr : r ∈ Ioo δ T) : r ∈ Ico (0 : ℝ) T :=
    ⟨hδ0.trans hr.1.le, hr.2⟩
  have hfront_subset : {z : ℝ × Vec | z.1 ∈ Ioo δ T} ⊆
      initialFrontSpacetime T := by
    intro z hz
    exact ⟨hδ0.trans hz.1.le, hz.2⟩
  have htail_subset : {z : ℝ × Vec | z.1 ∈ Ioo δ T} ⊆
      tailSpacetime δ := by
    intro z hz
    exact hz.1.le
  have hu_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      {z : ℝ × Vec | z.1 ∈ Ioo δ T} := H.velocity_smooth.mono hfront_subset
  have hv_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => v z.1 z.2)
      {z : ℝ × Vec | z.1 ∈ Ioo δ T} := K.velocity_smooth.mono htail_subset
  have huv : ∀ r ∈ Ioo δ T, u r = v r := by
    intro r hr
    apply continuous_periodic_field_eq_of_cube_ae
      (velocity_slice_contDiff_on_open_time_set isOpen_Ioo hu_smooth hr).continuous
      (velocity_slice_contDiff_on_open_time_set isOpen_Ioo hv_smooth hr).continuous
      (H.velocity_periodic r (hfront_time r hr)) (K.velocity_periodic r hr.1.le)
    exact (hfront_agrees r hr).symm.trans (htail_agrees r hr)
  refine ⟨huv, ?_⟩
  apply normalized_pressure_eq_on_jointly_smooth_velocity_overlap isOpen_Ioo huv
  · intro r hr
    exact H.equation r (hfront_time r hr)
  · intro r hr
    exact K.equation r hr.1.le
  · exact H.pressure_smooth.mono hfront_subset
  · exact K.pressure_smooth.mono htail_subset
  · intro r hr
    exact H.pressure_mean_zero r (hfront_time r hr)
  · intro r hr
    exact K.pressure_mean_zero r hr.1.le

end
end MethbokeAddon.WeakFouriermanB
