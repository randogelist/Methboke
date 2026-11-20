import FDSNLocalizedCoefficient.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open scoped ContDiff Topology

/- contDiff_mul_of_tsupport_subset. -/
example {f g : ℝ → ℂ} {S : Set ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiffOn ℝ ∞ g S)
    (hS : IsOpen S) (hfs : tsupport f ⊆ S) :
    ContDiff ℝ ∞ (fun t => f t * g t) :=
  MethbokeAddon.FDSN.contDiff_mul_of_tsupport_subset hf hg hS hfs

/- contDiff_timePhaseIncrement_mul_localCoefficient_joint: phase expanded. -/
example {β : ℝ → ℝ} {a : ℝ → ℂ} {s T : ℝ}
    (hβ : ContDiff ℝ ∞ β)
    (ha : ContDiffOn ℝ ∞ a (Set.Ioo s T))
    (hβs : tsupport β ⊆ Set.Ioo s T) :
    ContDiff ℝ ∞
      (fun q : ℝ × ℝ =>
        (Complex.exp (((q.1 * β q.2 : ℝ) : ℂ) * Complex.I) - 1) * a q.2) :=
  MethbokeAddon.FDSN.contDiff_timePhaseIncrement_mul_localCoefficient_joint hβ ha hβs

/- tsupport_timePhaseIncrement_mul_coefficient_subset. -/
example (β : ℝ → ℝ) (a : ℝ → ℂ) (lambda : ℝ) :
    tsupport (fun t : ℝ =>
      (Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I) - 1) * a t) ⊆ tsupport β :=
  MethbokeAddon.FDSN.tsupport_timePhaseIncrement_mul_coefficient_subset β a lambda

/- hasCompactSupport_timePhaseIncrement_mul_coefficient. -/
example {β : ℝ → ℝ} (hβ : HasCompactSupport β) (a : ℝ → ℂ) (lambda : ℝ) :
    HasCompactSupport (fun t : ℝ =>
      (Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I) - 1) * a t) :=
  MethbokeAddon.FDSN.hasCompactSupport_timePhaseIncrement_mul_coefficient hβ a lambda

/- localized_coefficient_uniform_linear_bound: full literal bound. -/
example {β : ℝ → ℝ} {a : ℝ → ℂ} {s T : ℝ}
    (hβcompact : HasCompactSupport β)
    (hβbounds : ∀ t : ℝ, 0 ≤ β t ∧ β t ≤ 1)
    (hβs : tsupport β ⊆ Set.Ioo s T)
    (ha : ContinuousOn a (Set.Ioo s T)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ lambda t : ℝ,
        ‖(Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I) - 1) * a t‖ ≤ C * ‖lambda‖ :=
  MethbokeAddon.FDSN.localized_coefficient_uniform_linear_bound
    hβcompact hβbounds hβs ha

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.contDiff_mul_of_tsupport_subset"
#check @MethbokeAddon.FDSN.contDiff_mul_of_tsupport_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.contDiff_mul_of_tsupport_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.contDiff_mul_of_tsupport_subset"
#print axioms MethbokeAddon.FDSN.contDiff_mul_of_tsupport_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.contDiff_mul_of_tsupport_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.contDiff_timePhaseIncrement_mul_localCoefficient_joint"
#check @MethbokeAddon.FDSN.contDiff_timePhaseIncrement_mul_localCoefficient_joint
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.contDiff_timePhaseIncrement_mul_localCoefficient_joint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.contDiff_timePhaseIncrement_mul_localCoefficient_joint"
#print axioms MethbokeAddon.FDSN.contDiff_timePhaseIncrement_mul_localCoefficient_joint
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.contDiff_timePhaseIncrement_mul_localCoefficient_joint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.tsupport_timePhaseIncrement_mul_coefficient_subset"
#check @MethbokeAddon.FDSN.tsupport_timePhaseIncrement_mul_coefficient_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.tsupport_timePhaseIncrement_mul_coefficient_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.tsupport_timePhaseIncrement_mul_coefficient_subset"
#print axioms MethbokeAddon.FDSN.tsupport_timePhaseIncrement_mul_coefficient_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.tsupport_timePhaseIncrement_mul_coefficient_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.hasCompactSupport_timePhaseIncrement_mul_coefficient"
#check @MethbokeAddon.FDSN.hasCompactSupport_timePhaseIncrement_mul_coefficient
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.hasCompactSupport_timePhaseIncrement_mul_coefficient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.hasCompactSupport_timePhaseIncrement_mul_coefficient"
#print axioms MethbokeAddon.FDSN.hasCompactSupport_timePhaseIncrement_mul_coefficient
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.hasCompactSupport_timePhaseIncrement_mul_coefficient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localized_coefficient_uniform_linear_bound"
#check @MethbokeAddon.FDSN.localized_coefficient_uniform_linear_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localized_coefficient_uniform_linear_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localized_coefficient_uniform_linear_bound"
#print axioms MethbokeAddon.FDSN.localized_coefficient_uniform_linear_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localized_coefficient_uniform_linear_bound"

