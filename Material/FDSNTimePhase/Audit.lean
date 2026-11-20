import FDSNTimePhase.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open scoped ContDiff Topology ComplexConjugate

/- Every public declaration has an independent literal consumer. -/

/- timePhase: definition equation. -/
example (β : ℝ → ℝ) (lambda t : ℝ) :
    MethbokeAddon.FDSN.timePhase β lambda t =
      Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I) := rfl

/- timePhaseIncrement: definition equation. -/
example (β : ℝ → ℝ) (lambda t : ℝ) :
    MethbokeAddon.FDSN.timePhaseIncrement β lambda t =
      Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I) - 1 := rfl

/- contDiff_phase. -/
example :
    ContDiff ℝ ∞ (fun theta : ℝ => Complex.exp ((theta : ℂ) * Complex.I)) :=
  MethbokeAddon.FDSN.contDiff_phase

/- contDiff_timePhase. -/
example {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (lambda : ℝ) :
    ContDiff ℝ ∞
      (fun t : ℝ => Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I)) :=
  MethbokeAddon.FDSN.contDiff_timePhase hβ lambda

/- contDiff_timePhase_joint. -/
example {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞
      (fun q : ℝ × ℝ => Complex.exp (((q.1 * β q.2 : ℝ) : ℂ) * Complex.I)) :=
  MethbokeAddon.FDSN.contDiff_timePhase_joint hβ

/- contDiff_timePhaseIncrement. -/
example {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (lambda : ℝ) :
    ContDiff ℝ ∞
      (fun t : ℝ => Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I) - 1) :=
  MethbokeAddon.FDSN.contDiff_timePhaseIncrement hβ lambda

/- contDiff_timePhaseIncrement_joint. -/
example {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞
      (fun q : ℝ × ℝ => Complex.exp (((q.1 * β q.2 : ℝ) : ℂ) * Complex.I) - 1) :=
  MethbokeAddon.FDSN.contDiff_timePhaseIncrement_joint hβ

/- timePhase_zero_parameter. -/
example (β : ℝ → ℝ) (t : ℝ) :
    Complex.exp ((((0 : ℝ) * β t : ℝ) : ℂ) * Complex.I) = 1 :=
  MethbokeAddon.FDSN.timePhase_zero_parameter β t

/- timePhaseIncrement_zero_parameter. -/
example (β : ℝ → ℝ) (t : ℝ) :
    Complex.exp ((((0 : ℝ) * β t : ℝ) : ℂ) * Complex.I) - 1 = 0 :=
  MethbokeAddon.FDSN.timePhaseIncrement_zero_parameter β t

/- timePhase_at_normalization. -/
example {β : ℝ → ℝ} {t : ℝ} (hβt : β t = 1) (lambda : ℝ) :
    Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((lambda : ℂ) * Complex.I) :=
  MethbokeAddon.FDSN.timePhase_at_normalization hβt lambda

/- timePhase_eq_one_of_notMem_tsupport. -/
example {β : ℝ → ℝ} {t : ℝ} (ht : t ∉ tsupport β) (lambda : ℝ) :
    Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I) = 1 :=
  MethbokeAddon.FDSN.timePhase_eq_one_of_notMem_tsupport ht lambda

/- tsupport_timePhaseIncrement_subset. -/
example (β : ℝ → ℝ) (lambda : ℝ) :
    tsupport (fun t : ℝ =>
      Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I) - 1) ⊆ tsupport β :=
  MethbokeAddon.FDSN.tsupport_timePhaseIncrement_subset β lambda

/- hasCompactSupport_timePhaseIncrement. -/
example {β : ℝ → ℝ} (hβ : HasCompactSupport β) (lambda : ℝ) :
    HasCompactSupport (fun t : ℝ =>
      Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I) - 1) :=
  MethbokeAddon.FDSN.hasCompactSupport_timePhaseIncrement hβ lambda

/- tsupport_deriv_timePhaseIncrement_subset. -/
example (β : ℝ → ℝ) (lambda : ℝ) :
    tsupport (deriv (fun t : ℝ =>
      Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I) - 1)) ⊆ tsupport β :=
  MethbokeAddon.FDSN.tsupport_deriv_timePhaseIncrement_subset β lambda

/- hasCompactSupport_deriv_timePhaseIncrement. -/
example {β : ℝ → ℝ} (hβ : HasCompactSupport β) (lambda : ℝ) :
    HasCompactSupport (deriv (fun t : ℝ =>
      Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I) - 1)) :=
  MethbokeAddon.FDSN.hasCompactSupport_deriv_timePhaseIncrement hβ lambda

/- norm_timePhase. -/
example (β : ℝ → ℝ) (lambda t : ℝ) :
    ‖Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I)‖ = 1 :=
  MethbokeAddon.FDSN.norm_timePhase β lambda t

/- norm_timePhaseIncrement_le. -/
example (β : ℝ → ℝ) (lambda t : ℝ) :
    ‖Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I) - 1‖ ≤
      ‖lambda‖ * ‖β t‖ :=
  MethbokeAddon.FDSN.norm_timePhaseIncrement_le β lambda t

/- norm_timePhaseIncrement_le_parameter. -/
example {β : ℝ → ℝ} {t : ℝ}
    (hβ0 : 0 ≤ β t) (hβ1 : β t ≤ 1) (lambda : ℝ) :
    ‖Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I) - 1‖ ≤ ‖lambda‖ :=
  MethbokeAddon.FDSN.norm_timePhaseIncrement_le_parameter hβ0 hβ1 lambda

/- timePhase_triad_separates: correlation and phase definitions expanded. -/
example {β : ℝ → ℝ} {t : ℝ} (hβt : β t = 1)
    {a b c : ℂ} (hB : a * b * conj c ≠ 0)
    {lambda eta : ℝ}
    (hlambda : |lambda| < Real.pi / 4) (heta : |eta| < Real.pi / 4)
    (hne : lambda ≠ eta) :
    a * b * conj (Complex.exp (((lambda * β t : ℝ) : ℂ) * Complex.I) * c) ≠
      a * b * conj (Complex.exp (((eta * β t : ℝ) : ℂ) * Complex.I) * c) :=
  MethbokeAddon.FDSN.timePhase_triad_separates hβt hB hlambda heta hne

/- exists_localized_time_phase_family: full literal contract. -/
example {s t T : ℝ} (hst : s < t) (htT : t < T) :
    ∃ β : ℝ → ℝ,
      ContDiff ℝ ∞ β ∧
      HasCompactSupport β ∧
      tsupport β ⊆ Set.Ioo s T ∧
      β t = 1 ∧
      (∀ u : ℝ, 0 ≤ β u ∧ β u ≤ 1) ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℝ =>
        Complex.exp (((q.1 * β q.2 : ℝ) : ℂ) * Complex.I)) ∧
      ∀ lambda : ℝ,
        HasCompactSupport (fun u : ℝ =>
          Complex.exp (((lambda * β u : ℝ) : ℂ) * Complex.I) - 1) ∧
        tsupport (fun u : ℝ =>
          Complex.exp (((lambda * β u : ℝ) : ℂ) * Complex.I) - 1) ⊆ Set.Ioo s T ∧
        tsupport (deriv (fun u : ℝ =>
          Complex.exp (((lambda * β u : ℝ) : ℂ) * Complex.I) - 1)) ⊆ Set.Ioo s T ∧
        ∀ u : ℝ,
          ‖Complex.exp (((lambda * β u : ℝ) : ℂ) * Complex.I) - 1‖ ≤ ‖lambda‖ :=
  MethbokeAddon.FDSN.exists_localized_time_phase_family hst htT

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.timePhase"
#check @MethbokeAddon.FDSN.timePhase
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.timePhase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.timePhase"
#print axioms MethbokeAddon.FDSN.timePhase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.timePhase"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.timePhaseIncrement"
#check @MethbokeAddon.FDSN.timePhaseIncrement
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.timePhaseIncrement"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.timePhaseIncrement"
#print axioms MethbokeAddon.FDSN.timePhaseIncrement
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.timePhaseIncrement"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.contDiff_phase"
#check @MethbokeAddon.FDSN.contDiff_phase
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.contDiff_phase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.contDiff_phase"
#print axioms MethbokeAddon.FDSN.contDiff_phase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.contDiff_phase"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.contDiff_timePhase"
#check @MethbokeAddon.FDSN.contDiff_timePhase
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.contDiff_timePhase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.contDiff_timePhase"
#print axioms MethbokeAddon.FDSN.contDiff_timePhase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.contDiff_timePhase"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.contDiff_timePhase_joint"
#check @MethbokeAddon.FDSN.contDiff_timePhase_joint
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.contDiff_timePhase_joint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.contDiff_timePhase_joint"
#print axioms MethbokeAddon.FDSN.contDiff_timePhase_joint
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.contDiff_timePhase_joint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.contDiff_timePhaseIncrement"
#check @MethbokeAddon.FDSN.contDiff_timePhaseIncrement
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.contDiff_timePhaseIncrement"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.contDiff_timePhaseIncrement"
#print axioms MethbokeAddon.FDSN.contDiff_timePhaseIncrement
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.contDiff_timePhaseIncrement"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.contDiff_timePhaseIncrement_joint"
#check @MethbokeAddon.FDSN.contDiff_timePhaseIncrement_joint
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.contDiff_timePhaseIncrement_joint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.contDiff_timePhaseIncrement_joint"
#print axioms MethbokeAddon.FDSN.contDiff_timePhaseIncrement_joint
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.contDiff_timePhaseIncrement_joint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.timePhase_zero_parameter"
#check @MethbokeAddon.FDSN.timePhase_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.timePhase_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.timePhase_zero_parameter"
#print axioms MethbokeAddon.FDSN.timePhase_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.timePhase_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.timePhaseIncrement_zero_parameter"
#check @MethbokeAddon.FDSN.timePhaseIncrement_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.timePhaseIncrement_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.timePhaseIncrement_zero_parameter"
#print axioms MethbokeAddon.FDSN.timePhaseIncrement_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.timePhaseIncrement_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.timePhase_at_normalization"
#check @MethbokeAddon.FDSN.timePhase_at_normalization
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.timePhase_at_normalization"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.timePhase_at_normalization"
#print axioms MethbokeAddon.FDSN.timePhase_at_normalization
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.timePhase_at_normalization"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.timePhase_eq_one_of_notMem_tsupport"
#check @MethbokeAddon.FDSN.timePhase_eq_one_of_notMem_tsupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.timePhase_eq_one_of_notMem_tsupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.timePhase_eq_one_of_notMem_tsupport"
#print axioms MethbokeAddon.FDSN.timePhase_eq_one_of_notMem_tsupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.timePhase_eq_one_of_notMem_tsupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.tsupport_timePhaseIncrement_subset"
#check @MethbokeAddon.FDSN.tsupport_timePhaseIncrement_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.tsupport_timePhaseIncrement_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.tsupport_timePhaseIncrement_subset"
#print axioms MethbokeAddon.FDSN.tsupport_timePhaseIncrement_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.tsupport_timePhaseIncrement_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.hasCompactSupport_timePhaseIncrement"
#check @MethbokeAddon.FDSN.hasCompactSupport_timePhaseIncrement
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.hasCompactSupport_timePhaseIncrement"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.hasCompactSupport_timePhaseIncrement"
#print axioms MethbokeAddon.FDSN.hasCompactSupport_timePhaseIncrement
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.hasCompactSupport_timePhaseIncrement"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.tsupport_deriv_timePhaseIncrement_subset"
#check @MethbokeAddon.FDSN.tsupport_deriv_timePhaseIncrement_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.tsupport_deriv_timePhaseIncrement_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.tsupport_deriv_timePhaseIncrement_subset"
#print axioms MethbokeAddon.FDSN.tsupport_deriv_timePhaseIncrement_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.tsupport_deriv_timePhaseIncrement_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.hasCompactSupport_deriv_timePhaseIncrement"
#check @MethbokeAddon.FDSN.hasCompactSupport_deriv_timePhaseIncrement
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.hasCompactSupport_deriv_timePhaseIncrement"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.hasCompactSupport_deriv_timePhaseIncrement"
#print axioms MethbokeAddon.FDSN.hasCompactSupport_deriv_timePhaseIncrement
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.hasCompactSupport_deriv_timePhaseIncrement"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.norm_timePhase"
#check @MethbokeAddon.FDSN.norm_timePhase
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.norm_timePhase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.norm_timePhase"
#print axioms MethbokeAddon.FDSN.norm_timePhase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.norm_timePhase"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.norm_timePhaseIncrement_le"
#check @MethbokeAddon.FDSN.norm_timePhaseIncrement_le
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.norm_timePhaseIncrement_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.norm_timePhaseIncrement_le"
#print axioms MethbokeAddon.FDSN.norm_timePhaseIncrement_le
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.norm_timePhaseIncrement_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.norm_timePhaseIncrement_le_parameter"
#check @MethbokeAddon.FDSN.norm_timePhaseIncrement_le_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.norm_timePhaseIncrement_le_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.norm_timePhaseIncrement_le_parameter"
#print axioms MethbokeAddon.FDSN.norm_timePhaseIncrement_le_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.norm_timePhaseIncrement_le_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.timePhase_triad_separates"
#check @MethbokeAddon.FDSN.timePhase_triad_separates
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.timePhase_triad_separates"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.timePhase_triad_separates"
#print axioms MethbokeAddon.FDSN.timePhase_triad_separates
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.timePhase_triad_separates"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.exists_localized_time_phase_family"
#check @MethbokeAddon.FDSN.exists_localized_time_phase_family
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.exists_localized_time_phase_family"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.exists_localized_time_phase_family"
#print axioms MethbokeAddon.FDSN.exists_localized_time_phase_family
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.exists_localized_time_phase_family"

