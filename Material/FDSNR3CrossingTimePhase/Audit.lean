import FDSNR3CrossingTimePhase.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory SingularClosure MethbokeAddon.FDSNR3
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology

example (ρ : ℝ → ℝ) (tstar tzero t : ℝ) :
    crossingTimePhase ρ tstar tzero t =
      ((t - tzero) / (tstar - tzero)) * ρ t := rfl

example : ∀ (ρ : ℝ → ℝ) (tstar tzero : ℝ),
    crossingTimePhase ρ tstar tzero tzero = 0 :=
  @crossingTimePhase_at_zero

example : ∀ {ρ : ℝ → ℝ} {tstar tzero : ℝ}
    (hρ : ρ tstar = 1) (hne : tzero ≠ tstar),
    crossingTimePhase ρ tstar tzero tstar = 1 :=
  @crossingTimePhase_at_normalization

example : ∀ {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (tstar tzero : ℝ),
    ContDiff ℝ ∞ (crossingTimePhase ρ tstar tzero) :=
  @crossingTimePhase_contDiff

example : ∀ (ρ : ℝ → ℝ) (tstar tzero : ℝ),
    tsupport (crossingTimePhase ρ tstar tzero) ⊆ tsupport ρ :=
  @crossingTimePhase_tsupport_subset

example : ∀ {ρ : ℝ → ℝ}
    (hρ : HasCompactSupport ρ) (tstar tzero : ℝ),
    HasCompactSupport (crossingTimePhase ρ tstar tzero) :=
  @crossingTimePhase_hasCompactSupport

example : ∀ {ρ : ℝ → ℝ}
    (hρ : Differentiable ℝ ρ) (tstar tzero : ℝ),
    HasDerivAt (crossingTimePhase ρ tstar tzero)
      (ρ tzero / (tstar - tzero)) tzero :=
  @crossingTimePhase_hasDerivAt_zero

example : ∀ {ρ : ℝ → ℝ}
    (hρ : Differentiable ℝ ρ) {tstar tzero : ℝ}
    (hne : tzero ≠ tstar) (hρzero : ρ tzero ≠ 0),
    deriv (crossingTimePhase ρ tstar tzero) tzero ≠ 0 :=
  @crossingTimePhase_deriv_ne_zero

example : ∀ {a b tstar : ℝ} (ha : a < tstar) (hb : tstar < b)
    {ρ : ℝ → ℝ} (hρ : ContinuousAt ρ tstar) (hρstar : ρ tstar = 1)
    {c : ℝ → ℂ} (hc : ContinuousAt c tstar) (hcstar : c tstar ≠ 0),
    ∃ tzero ∈ Ioo a b, tzero ≠ tstar ∧ ρ tzero ≠ 0 ∧ c tzero ≠ 0 :=
  @exists_nearby_nonzero_crossing_time

example : ∀ {a b tstar : ℝ} (ha : a < tstar) (hb : tstar < b)
    {c : ℝ → ℂ} (hc : ContinuousAt c tstar) (hcstar : c tstar ≠ 0),
    ∃ tzero : ℝ, ∃ β : ℝ → ℝ, ∃ slope : ℝ,
      tzero ∈ Ioo a b ∧ tzero ≠ tstar ∧ c tzero ≠ 0 ∧
      ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ Ioo a b ∧
      β tstar = 1 ∧ β tzero = 0 ∧ HasDerivAt β slope tzero ∧ slope ≠ 0 :=
  @exists_signed_crossing_time_phase

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase"
#check @MethbokeAddon.FDSNR3.crossingTimePhase
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.crossingTimePhase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase"
#print axioms MethbokeAddon.FDSNR3.crossingTimePhase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.crossingTimePhase"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase_at_zero"
#check @MethbokeAddon.FDSNR3.crossingTimePhase_at_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.crossingTimePhase_at_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase_at_zero"
#print axioms MethbokeAddon.FDSNR3.crossingTimePhase_at_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.crossingTimePhase_at_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase_at_normalization"
#check @MethbokeAddon.FDSNR3.crossingTimePhase_at_normalization
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.crossingTimePhase_at_normalization"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase_at_normalization"
#print axioms MethbokeAddon.FDSNR3.crossingTimePhase_at_normalization
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.crossingTimePhase_at_normalization"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase_contDiff"
#check @MethbokeAddon.FDSNR3.crossingTimePhase_contDiff
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.crossingTimePhase_contDiff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase_contDiff"
#print axioms MethbokeAddon.FDSNR3.crossingTimePhase_contDiff
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.crossingTimePhase_contDiff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase_tsupport_subset"
#check @MethbokeAddon.FDSNR3.crossingTimePhase_tsupport_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.crossingTimePhase_tsupport_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase_tsupport_subset"
#print axioms MethbokeAddon.FDSNR3.crossingTimePhase_tsupport_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.crossingTimePhase_tsupport_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase_hasCompactSupport"
#check @MethbokeAddon.FDSNR3.crossingTimePhase_hasCompactSupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.crossingTimePhase_hasCompactSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase_hasCompactSupport"
#print axioms MethbokeAddon.FDSNR3.crossingTimePhase_hasCompactSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.crossingTimePhase_hasCompactSupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase_hasDerivAt_zero"
#check @MethbokeAddon.FDSNR3.crossingTimePhase_hasDerivAt_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.crossingTimePhase_hasDerivAt_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase_hasDerivAt_zero"
#print axioms MethbokeAddon.FDSNR3.crossingTimePhase_hasDerivAt_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.crossingTimePhase_hasDerivAt_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase_deriv_ne_zero"
#check @MethbokeAddon.FDSNR3.crossingTimePhase_deriv_ne_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.crossingTimePhase_deriv_ne_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.crossingTimePhase_deriv_ne_zero"
#print axioms MethbokeAddon.FDSNR3.crossingTimePhase_deriv_ne_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.crossingTimePhase_deriv_ne_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.exists_nearby_nonzero_crossing_time"
#check @MethbokeAddon.FDSNR3.exists_nearby_nonzero_crossing_time
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.exists_nearby_nonzero_crossing_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.exists_nearby_nonzero_crossing_time"
#print axioms MethbokeAddon.FDSNR3.exists_nearby_nonzero_crossing_time
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.exists_nearby_nonzero_crossing_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.exists_signed_crossing_time_phase"
#check @MethbokeAddon.FDSNR3.exists_signed_crossing_time_phase
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.exists_signed_crossing_time_phase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.exists_signed_crossing_time_phase"
#print axioms MethbokeAddon.FDSNR3.exists_signed_crossing_time_phase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.exists_signed_crossing_time_phase"

