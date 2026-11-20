import FDSNR3FrequencyCutoff.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section
open Set Metric SingularClosure MethbokeAddon.FDSNR3
open scoped ContDiff Topology

example (c : Vec) (r : ℝ) (hr : 0 < r) :
    frequencyBump c r hr =
      ({ rIn := r / 8, rOut := r / 4,
         rIn_pos := by positivity,
         rIn_lt_rOut := by linarith } : ContDiffBump c) := rfl

example : (frequencyAnchor : Vec → ℝ → Vec) =
    (fun c r => c + (r / 2) • unitVector (0 : Fin 3)) := rfl

example (c : Vec) (r : ℝ) (hr : 0 < r) :
    oddFrequencyCutoff c r hr =
      (fun ξ : Vec => frequencyBump c r hr ξ - frequencyBump c r hr (-ξ)) := rfl

example : ∀ (c : Vec) {r : ℝ} (hr : 0 ≤ r),
    dist (frequencyAnchor c r) c = r / 2 :=
  @dist_frequencyAnchor

example : ∀ (c : Vec),
    dist c (-c) = 2 * ‖c‖ :=
  @dist_self_neg_frequency

example : ∀ (c ξ : Vec),
    dist (-ξ) c = dist ξ (-c) :=
  @reflected_frequency_dist

example : ∀ {c : Vec} {r : ℝ} (hr : 0 < r),
    closedBall c (r / 16) ⊆ ball c r :=
  @active_closedBall_subset

example : ∀ {c : Vec} {r : ℝ} (hr : 0 < r),
    closedBall (frequencyAnchor c r) (r / 16) ⊆ ball c r :=
  @anchor_closedBall_subset

example : ∀ {c : Vec} {r : ℝ} (hr : 0 < r),
    Disjoint (closedBall c (r / 16))
      (closedBall (frequencyAnchor c r) (r / 16)) :=
  @active_anchor_closedBall_disjoint

example : ∀ {c : Vec} {r : ℝ} (hr : 0 < r) (haway : r < ‖c‖)
    {ξ : Vec} (hξ : ξ ∈ ball c r),
    frequencyBump c r hr (-ξ) = 0 :=
  @frequencyBump_reflected_eq_zero

example : ∀ (c : Vec) (r : ℝ) (hr : 0 < r),
    ContDiff ℝ ∞ (oddFrequencyCutoff c r hr) :=
  @oddFrequencyCutoff_contDiff

example : ∀ (c : Vec) (r : ℝ) (hr : 0 < r) (ξ : Vec),
    oddFrequencyCutoff c r hr (-ξ) = -oddFrequencyCutoff c r hr ξ :=
  @oddFrequencyCutoff_odd

example : ∀ (c : Vec) (r : ℝ) (hr : 0 < r) (ξ : Vec),
    |oddFrequencyCutoff c r hr ξ| ≤ 1 :=
  @oddFrequencyCutoff_abs_le_one

example : ∀ {c : Vec} {r : ℝ} (hr : 0 < r) (haway : r < ‖c‖)
    {ξ : Vec} (hξ : ξ ∈ closedBall c (r / 16)),
    oddFrequencyCutoff c r hr ξ = 1 :=
  @oddFrequencyCutoff_eq_one_on_active

example : ∀ {c : Vec} {r : ℝ} (hr : 0 < r) (haway : r < ‖c‖)
    {ξ : Vec} (hξ : ξ ∈ closedBall (frequencyAnchor c r) (r / 16)),
    oddFrequencyCutoff c r hr ξ = 0 :=
  @oddFrequencyCutoff_eq_zero_on_anchor

example : ∀ {c : Vec} {r : ℝ} (hr : 0 < r) (haway : r < ‖c‖)
    {ξ : Vec} (hξ : ‖ξ‖ < ‖c‖ / 2),
    oddFrequencyCutoff c r hr ξ = 0 :=
  @oddFrequencyCutoff_eq_zero_of_small_norm

example : ∀ (c : Vec) (r : ℝ) (hr : 0 < r),
    tsupport (oddFrequencyCutoff c r hr) ⊆
      closedBall c (r / 4) ∪ closedBall (-c) (r / 4) :=
  @oddFrequencyCutoff_tsupport_subset

example : ∀ (c : Vec) (r : ℝ) (hr : 0 < r),
    HasCompactSupport (oddFrequencyCutoff c r hr) :=
  @oddFrequencyCutoff_hasCompactSupport

example : ∀ {c : Vec} {r : ℝ} (hr : 0 < r) (haway : r < ‖c‖),
    (0 : Vec) ∉ tsupport (oddFrequencyCutoff c r hr) :=
  @oddFrequencyCutoff_zero_notMem_tsupport

example : ∀ {c : Vec} {r : ℝ} (hr : 0 < r) (haway : r < ‖c‖),
    ∃ ψ : Vec → ℝ, ∃ b : Vec, ∃ δ ρ : ℝ,
      0 < δ ∧ 0 < ρ ∧
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ ξ : Vec, ψ (-ξ) = -ψ ξ) ∧
      (∀ ξ : Vec, |ψ ξ| ≤ 1) ∧
      closedBall c δ ⊆ ball c r ∧
      closedBall b δ ⊆ ball c r ∧
      Disjoint (closedBall c δ) (closedBall b δ) ∧
      (∀ ξ ∈ closedBall c δ, ψ ξ = 1) ∧
      (∀ ξ ∈ closedBall b δ, ψ ξ = 0) ∧
      (∀ ξ : Vec, ‖ξ‖ < ρ → ψ ξ = 0) ∧
      (0 : Vec) ∉ tsupport ψ :=
  @exists_odd_frequency_cutoff

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.frequencyBump"
#check @MethbokeAddon.FDSNR3.frequencyBump
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.frequencyBump"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.frequencyBump"
#print axioms MethbokeAddon.FDSNR3.frequencyBump
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.frequencyBump"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.frequencyAnchor"
#check @MethbokeAddon.FDSNR3.frequencyAnchor
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.frequencyAnchor"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.frequencyAnchor"
#print axioms MethbokeAddon.FDSNR3.frequencyAnchor
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.frequencyAnchor"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff"
#check @MethbokeAddon.FDSNR3.oddFrequencyCutoff
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff"
#print axioms MethbokeAddon.FDSNR3.oddFrequencyCutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.dist_frequencyAnchor"
#check @MethbokeAddon.FDSNR3.dist_frequencyAnchor
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.dist_frequencyAnchor"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.dist_frequencyAnchor"
#print axioms MethbokeAddon.FDSNR3.dist_frequencyAnchor
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.dist_frequencyAnchor"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.dist_self_neg_frequency"
#check @MethbokeAddon.FDSNR3.dist_self_neg_frequency
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.dist_self_neg_frequency"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.dist_self_neg_frequency"
#print axioms MethbokeAddon.FDSNR3.dist_self_neg_frequency
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.dist_self_neg_frequency"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.reflected_frequency_dist"
#check @MethbokeAddon.FDSNR3.reflected_frequency_dist
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.reflected_frequency_dist"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.reflected_frequency_dist"
#print axioms MethbokeAddon.FDSNR3.reflected_frequency_dist
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.reflected_frequency_dist"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.active_closedBall_subset"
#check @MethbokeAddon.FDSNR3.active_closedBall_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.active_closedBall_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.active_closedBall_subset"
#print axioms MethbokeAddon.FDSNR3.active_closedBall_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.active_closedBall_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.anchor_closedBall_subset"
#check @MethbokeAddon.FDSNR3.anchor_closedBall_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.anchor_closedBall_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.anchor_closedBall_subset"
#print axioms MethbokeAddon.FDSNR3.anchor_closedBall_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.anchor_closedBall_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.active_anchor_closedBall_disjoint"
#check @MethbokeAddon.FDSNR3.active_anchor_closedBall_disjoint
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.active_anchor_closedBall_disjoint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.active_anchor_closedBall_disjoint"
#print axioms MethbokeAddon.FDSNR3.active_anchor_closedBall_disjoint
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.active_anchor_closedBall_disjoint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.frequencyBump_reflected_eq_zero"
#check @MethbokeAddon.FDSNR3.frequencyBump_reflected_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.frequencyBump_reflected_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.frequencyBump_reflected_eq_zero"
#print axioms MethbokeAddon.FDSNR3.frequencyBump_reflected_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.frequencyBump_reflected_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_contDiff"
#check @MethbokeAddon.FDSNR3.oddFrequencyCutoff_contDiff
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_contDiff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_contDiff"
#print axioms MethbokeAddon.FDSNR3.oddFrequencyCutoff_contDiff
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_contDiff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_odd"
#check @MethbokeAddon.FDSNR3.oddFrequencyCutoff_odd
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_odd"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_odd"
#print axioms MethbokeAddon.FDSNR3.oddFrequencyCutoff_odd
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_odd"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_abs_le_one"
#check @MethbokeAddon.FDSNR3.oddFrequencyCutoff_abs_le_one
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_abs_le_one"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_abs_le_one"
#print axioms MethbokeAddon.FDSNR3.oddFrequencyCutoff_abs_le_one
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_abs_le_one"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_one_on_active"
#check @MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_one_on_active
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_one_on_active"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_one_on_active"
#print axioms MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_one_on_active
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_one_on_active"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_zero_on_anchor"
#check @MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_zero_on_anchor
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_zero_on_anchor"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_zero_on_anchor"
#print axioms MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_zero_on_anchor
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_zero_on_anchor"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_zero_of_small_norm"
#check @MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_zero_of_small_norm
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_zero_of_small_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_zero_of_small_norm"
#print axioms MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_zero_of_small_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_eq_zero_of_small_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_tsupport_subset"
#check @MethbokeAddon.FDSNR3.oddFrequencyCutoff_tsupport_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_tsupport_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_tsupport_subset"
#print axioms MethbokeAddon.FDSNR3.oddFrequencyCutoff_tsupport_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_tsupport_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_hasCompactSupport"
#check @MethbokeAddon.FDSNR3.oddFrequencyCutoff_hasCompactSupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_hasCompactSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_hasCompactSupport"
#print axioms MethbokeAddon.FDSNR3.oddFrequencyCutoff_hasCompactSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_hasCompactSupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_zero_notMem_tsupport"
#check @MethbokeAddon.FDSNR3.oddFrequencyCutoff_zero_notMem_tsupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_zero_notMem_tsupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.oddFrequencyCutoff_zero_notMem_tsupport"
#print axioms MethbokeAddon.FDSNR3.oddFrequencyCutoff_zero_notMem_tsupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.oddFrequencyCutoff_zero_notMem_tsupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.exists_odd_frequency_cutoff"
#check @MethbokeAddon.FDSNR3.exists_odd_frequency_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.exists_odd_frequency_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.exists_odd_frequency_cutoff"
#print axioms MethbokeAddon.FDSNR3.exists_odd_frequency_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.exists_odd_frequency_cutoff"

