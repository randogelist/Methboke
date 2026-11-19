import EhrenfestCanonicalErrorInequality.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-! Independent exact consumer types; external evidence pending. -/


section Consumer1
open Set SingularClosure
open MethbokeAddon.WeakFouriermanB
open MethbokeAddon.EhrenfestObstruction

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (S T : ℝ) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a.val u p) (hTS : T < S) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ n t, t ∈ Ioo (0 : ℝ) T →
      ∃ d : ℝ,
        HasDerivAt
          (fun r => coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n r))
          d t ∧
        d ≤ C * (coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n t) +
              (coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n t)) ^ 3) +
            A / (((n + 1 : ℕ) : ℝ) ^ 2) :=
  initial_front_canonical_error_differential_inequality ν hν a S T u p H hTS
end Consumer1


#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_canonical_error_differential_inequality"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_canonical_error_differential_inequality
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_canonical_error_differential_inequality"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_canonical_error_differential_inequality"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_canonical_error_differential_inequality
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_canonical_error_differential_inequality"
