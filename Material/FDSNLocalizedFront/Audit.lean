import FDSNLocalizedFront.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false

noncomputable section

open Set SingularClosure
open MethbokeAddon.FDSN
open scoped ContDiff Topology

example {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T) (lambda : ℝ) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec,
      timeDerivative (localizedPairVelocity a β u lambda) t x +
          convection (localizedPairVelocity a β u lambda t) x +
          SingularClosure.gradient (p t) x =
        ν • laplacian (localizedPairVelocity a β u lambda t) x +
          localizedPairForce ν a β u F lambda t x :=
  localizedPair_momentum h a hβ hβs lambda

example {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T) (lambda : ℝ) :
    PreterminalNSE ν T (localizedPairVelocity a β u lambda) p
      (localizedPairForce ν a β u F lambda) :=
  localizedPair_front h ha hβ hβs lambda

example {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T) (lambda : ℝ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => localizedPairVelocity a β u lambda z.1 z.2)
        {z | z.1 ∈ Ico (0 : ℝ) T} ∧
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) {z | z.1 ∈ Ico (0 : ℝ) T} ∧
    (∀ t ∈ Ico (0 : ℝ) T, SpatialPeriodic (localizedPairVelocity a β u lambda t)) ∧
    (∀ t ∈ Ico (0 : ℝ) T, SpatialPeriodic (p t)) ∧
    (∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec,
      divergence (localizedPairVelocity a β u lambda t) x = 0) ∧
    (∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec,
      timeDerivative (localizedPairVelocity a β u lambda) t x +
          convection (localizedPairVelocity a β u lambda t) x +
          SingularClosure.gradient (p t) x =
        ν • laplacian (localizedPairVelocity a β u lambda t) x +
          localizedPairForce ν a β u F lambda t x) := by
  have hfront := localizedPair_front h ha hβ hβs lambda
  exact ⟨hfront.velocity_smooth, hfront.pressure_smooth, hfront.velocity_periodic,
    hfront.pressure_periodic, hfront.divergence_free, hfront.equation⟩

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPair_momentum"
#check @MethbokeAddon.FDSN.localizedPair_momentum
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPair_momentum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPair_momentum"
#print axioms MethbokeAddon.FDSN.localizedPair_momentum
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPair_momentum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPair_front"
#check @MethbokeAddon.FDSN.localizedPair_front
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPair_front"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPair_front"
#print axioms MethbokeAddon.FDSN.localizedPair_front
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPair_front"

