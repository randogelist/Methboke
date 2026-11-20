import FDSNLocalizedSmallness.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false

noncomputable section

open Set SingularClosure
open MethbokeAddon.WeakFouriermanB MethbokeAddon.FeffermanFamily
open MethbokeAddon.EhrenfestObstruction MethbokeAddon.FDSN
open scoped ContDiff Topology

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T)
    (K : Set (ℝ × Vec)) (hK : IsCompact K) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lambda : ℝ, ‖lambda‖ ≤ 1 →
      ∀ n : ℕ, n ≤ r → ∀ z ∈ K,
        ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec =>
          (localizedPairVelocity a β u lambda - u) y.1 y.2) z‖ ≤ C * ‖lambda‖ :=
  localizedPairVelocity_finite_order_linear_bound h a hβ hβs K hK r

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T)
    (K : Set (ℝ × Vec)) (hK : IsCompact K) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lambda : ℝ, ‖lambda‖ ≤ 1 →
      ∀ n : ℕ, n ≤ r → ∀ z ∈ K,
        ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec =>
          (localizedPairForce ν a β u F lambda - F) y.1 y.2) z‖ ≤ C * ‖lambda‖ :=
  localizedPairForce_finite_order_linear_bound h a hβ hβs K hK r


#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_finite_order_linear_bound"
#check @MethbokeAddon.FDSN.localizedPairVelocity_finite_order_linear_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_finite_order_linear_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_finite_order_linear_bound"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_finite_order_linear_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_finite_order_linear_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairForce_finite_order_linear_bound"
#check @MethbokeAddon.FDSN.localizedPairForce_finite_order_linear_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairForce_finite_order_linear_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairForce_finite_order_linear_bound"
#print axioms MethbokeAddon.FDSN.localizedPairForce_finite_order_linear_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairForce_finite_order_linear_bound"

