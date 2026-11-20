import FDSNPhase.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/- Independent full-type consumers for every public Phase declaration.
   Root supplies the package import and its ordered audit sentinels. -/

noncomputable section
open scoped ComplexConjugate
open MethbokeAddon.FDSN

example : (phase : ℝ → ℂ) =
    (fun theta : ℝ => Complex.exp ((theta : ℂ) * Complex.I)) := rfl

example : phase 0 = 1 := phase_zero

example (theta eta : ℝ) :
    phase (theta + eta) = phase theta * phase eta := phase_add theta eta

example (theta : ℝ) : phase theta ≠ 0 := phase_ne_zero theta

example (theta : ℝ) : ‖phase theta‖ = 1 := norm_phase theta

example (theta : ℝ) : phase (-theta) = conj (phase theta) := phase_neg theta

example (theta : ℝ) : conj (phase theta) = phase (-theta) := conj_phase theta

example (theta : ℝ) : phase theta * phase (-theta) = 1 := phase_mul_neg theta

example (theta : ℝ) (z : ℂ) : ‖phase theta * z‖ = ‖z‖ := norm_phase_mul theta z

example (theta : ℝ) (z : ℂ) :
    ‖phase theta * z‖ ^ 2 = ‖z‖ ^ 2 := modal_power_phase_mul theta z

example (theta : ℝ) : ‖phase theta - 1‖ ≤ ‖theta‖ := norm_phase_sub_one_le theta

example (theta : ℝ) (z : ℂ) :
    ‖phase theta * z - z‖ ≤ ‖theta‖ * ‖z‖ := norm_phase_mul_sub_le theta z

example {theta eta : ℝ} (htheta : |theta| < Real.pi) (heta : |eta| < Real.pi)
    (h : phase theta = phase eta) : theta = eta :=
  phase_injective_of_abs_lt_pi htheta heta h

example {theta eta : ℝ} (htheta : |theta| < Real.pi / 4)
    (heta : |eta| < Real.pi / 4) (h : phase theta = phase eta) : theta = eta :=
  phase_injective_small htheta heta h

example : (triadCorrelation : ℂ → ℂ → ℂ → ℂ) =
    (fun a b c : ℂ => a * b * conj c) := rfl

example {a b c : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    triadCorrelation a b c ≠ 0 := triadCorrelation_ne_zero ha hb hc

example (a b c : ℂ) (theta : ℝ) :
    triadCorrelation a b (phase theta * c) =
      phase (-theta) * triadCorrelation a b c := triadCorrelation_phase a b c theta

example (a b c : ℂ) (alpha beta : ℝ) :
    triadCorrelation (phase alpha * a) (phase beta * b)
      (phase (alpha + beta) * c) = triadCorrelation a b c :=
  triadCorrelation_translation a b c alpha beta

example {a b c : ℂ} (hB : triadCorrelation a b c ≠ 0) {lambda eta : ℝ}
    (hlambda : |lambda| < Real.pi / 4) (heta : |eta| < Real.pi / 4)
    (hne : lambda ≠ eta) :
    triadCorrelation a b (phase lambda * c) ≠
      triadCorrelation a b (phase eta * c) :=
  triadCorrelation_phase_separates hB hlambda heta hne

example {a b c : ℂ} (hB : triadCorrelation a b c ≠ 0) {lambda eta : ℝ}
    (hlambda : |lambda| < Real.pi / 4) (heta : |eta| < Real.pi / 4)
    (hne : lambda ≠ eta) (alpha beta : ℝ) :
    ¬ (phase alpha * a = a ∧ phase beta * b = b ∧
      phase (alpha + beta) * (phase lambda * c) = phase eta * c) :=
  triad_phase_not_translation hB hlambda heta hne alpha beta

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.phase"
#check @MethbokeAddon.FDSN.phase
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.phase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.phase"
#print axioms MethbokeAddon.FDSN.phase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.phase"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.phase_zero"
#check @MethbokeAddon.FDSN.phase_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.phase_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.phase_zero"
#print axioms MethbokeAddon.FDSN.phase_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.phase_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.phase_add"
#check @MethbokeAddon.FDSN.phase_add
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.phase_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.phase_add"
#print axioms MethbokeAddon.FDSN.phase_add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.phase_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.phase_ne_zero"
#check @MethbokeAddon.FDSN.phase_ne_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.phase_ne_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.phase_ne_zero"
#print axioms MethbokeAddon.FDSN.phase_ne_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.phase_ne_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.norm_phase"
#check @MethbokeAddon.FDSN.norm_phase
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.norm_phase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.norm_phase"
#print axioms MethbokeAddon.FDSN.norm_phase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.norm_phase"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.phase_neg"
#check @MethbokeAddon.FDSN.phase_neg
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.phase_neg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.phase_neg"
#print axioms MethbokeAddon.FDSN.phase_neg
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.phase_neg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.conj_phase"
#check @MethbokeAddon.FDSN.conj_phase
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.conj_phase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.conj_phase"
#print axioms MethbokeAddon.FDSN.conj_phase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.conj_phase"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.phase_mul_neg"
#check @MethbokeAddon.FDSN.phase_mul_neg
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.phase_mul_neg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.phase_mul_neg"
#print axioms MethbokeAddon.FDSN.phase_mul_neg
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.phase_mul_neg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.norm_phase_mul"
#check @MethbokeAddon.FDSN.norm_phase_mul
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.norm_phase_mul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.norm_phase_mul"
#print axioms MethbokeAddon.FDSN.norm_phase_mul
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.norm_phase_mul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.modal_power_phase_mul"
#check @MethbokeAddon.FDSN.modal_power_phase_mul
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.modal_power_phase_mul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.modal_power_phase_mul"
#print axioms MethbokeAddon.FDSN.modal_power_phase_mul
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.modal_power_phase_mul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.norm_phase_sub_one_le"
#check @MethbokeAddon.FDSN.norm_phase_sub_one_le
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.norm_phase_sub_one_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.norm_phase_sub_one_le"
#print axioms MethbokeAddon.FDSN.norm_phase_sub_one_le
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.norm_phase_sub_one_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.norm_phase_mul_sub_le"
#check @MethbokeAddon.FDSN.norm_phase_mul_sub_le
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.norm_phase_mul_sub_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.norm_phase_mul_sub_le"
#print axioms MethbokeAddon.FDSN.norm_phase_mul_sub_le
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.norm_phase_mul_sub_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.phase_injective_of_abs_lt_pi"
#check @MethbokeAddon.FDSN.phase_injective_of_abs_lt_pi
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.phase_injective_of_abs_lt_pi"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.phase_injective_of_abs_lt_pi"
#print axioms MethbokeAddon.FDSN.phase_injective_of_abs_lt_pi
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.phase_injective_of_abs_lt_pi"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.phase_injective_small"
#check @MethbokeAddon.FDSN.phase_injective_small
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.phase_injective_small"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.phase_injective_small"
#print axioms MethbokeAddon.FDSN.phase_injective_small
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.phase_injective_small"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.triadCorrelation"
#check @MethbokeAddon.FDSN.triadCorrelation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.triadCorrelation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.triadCorrelation"
#print axioms MethbokeAddon.FDSN.triadCorrelation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.triadCorrelation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.triadCorrelation_ne_zero"
#check @MethbokeAddon.FDSN.triadCorrelation_ne_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.triadCorrelation_ne_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.triadCorrelation_ne_zero"
#print axioms MethbokeAddon.FDSN.triadCorrelation_ne_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.triadCorrelation_ne_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.triadCorrelation_phase"
#check @MethbokeAddon.FDSN.triadCorrelation_phase
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.triadCorrelation_phase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.triadCorrelation_phase"
#print axioms MethbokeAddon.FDSN.triadCorrelation_phase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.triadCorrelation_phase"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.triadCorrelation_translation"
#check @MethbokeAddon.FDSN.triadCorrelation_translation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.triadCorrelation_translation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.triadCorrelation_translation"
#print axioms MethbokeAddon.FDSN.triadCorrelation_translation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.triadCorrelation_translation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.triadCorrelation_phase_separates"
#check @MethbokeAddon.FDSN.triadCorrelation_phase_separates
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.triadCorrelation_phase_separates"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.triadCorrelation_phase_separates"
#print axioms MethbokeAddon.FDSN.triadCorrelation_phase_separates
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.triadCorrelation_phase_separates"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.triad_phase_not_translation"
#check @MethbokeAddon.FDSN.triad_phase_not_translation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.triad_phase_not_translation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.triad_phase_not_translation"
#print axioms MethbokeAddon.FDSN.triad_phase_not_translation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.triad_phase_not_translation"

