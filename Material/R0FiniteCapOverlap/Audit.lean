import R0FiniteCapOverlap.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology Interval

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.velocity_slice_contDiff_on_open_time_set
example : ∀ {u : Velocity} {I : Set ℝ} (hI : IsOpen I)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      {z : ℝ × Vec | z.1 ∈ I}) {t : ℝ} (ht : t ∈ I),
    ContDiff ℝ ∞ (u t) :=
  @MethbokeAddon.WeakFouriermanB.velocity_slice_contDiff_on_open_time_set

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.finite_cap_tail_overlap_of_same_path_ae
example : ∀ (ν T δ : ℝ) (a : Field) (u v w : Velocity) (p q : Pressure)
    (H : InitialClassicalFront ν T a u p) (K : ClassicalTail ν δ v q)
    (hδ0 : 0 ≤ δ)
    (hfront_agrees : ∀ r ∈ Ioo δ T, w r =ᵐ[volume.restrict unitCube] u r)
    (htail_agrees : ∀ r ∈ Ioo δ T, w r =ᵐ[volume.restrict unitCube] v r),
    (∀ r ∈ Ioo δ T, u r = v r) ∧ (∀ r ∈ Ioo δ T, p r = q r) :=
  @MethbokeAddon.WeakFouriermanB.finite_cap_tail_overlap_of_same_path_ae

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.velocity_slice_contDiff_on_open_time_set"
#check @MethbokeAddon.WeakFouriermanB.velocity_slice_contDiff_on_open_time_set
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.velocity_slice_contDiff_on_open_time_set"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.velocity_slice_contDiff_on_open_time_set"
#print axioms MethbokeAddon.WeakFouriermanB.velocity_slice_contDiff_on_open_time_set
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.velocity_slice_contDiff_on_open_time_set"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.finite_cap_tail_overlap_of_same_path_ae"
#check @MethbokeAddon.WeakFouriermanB.finite_cap_tail_overlap_of_same_path_ae
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.finite_cap_tail_overlap_of_same_path_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.finite_cap_tail_overlap_of_same_path_ae"
#print axioms MethbokeAddon.WeakFouriermanB.finite_cap_tail_overlap_of_same_path_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.finite_cap_tail_overlap_of_same_path_ae"

