import FDSNLocalizedForceSeparation.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/- Explicit full-type consumers; root supplies imports and audit sentinels. -/

noncomputable section
open Set SingularClosure MethbokeAddon.FDSN
open scoped ContDiff Topology

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (hsβ : s ∉ tsupport β) (hβt : β t = 1) (i : Fin 3)
    (hcoeff : datumFourierCoeff (u t) a i ≠ 0)
    {lambda eta : ℝ} (hlambda : |lambda| < Real.pi / 4)
    (heta : |eta| < Real.pi / 4) (hne : lambda ≠ eta),
    ∃ r ∈ Ioo s t,
      coefficientLeray a (datumFourierCoeff (localizedPairForce ν a β u F lambda r) a) i ≠
        coefficientLeray a (datumFourierCoeff (localizedPairForce ν a β u F eta r) a) i :=
  @MethbokeAddon.FDSN.localizedPairForce_projected_separates

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (hsβ : s ∉ tsupport β) (hβt : β t = 1) (i : Fin 3)
    (hcoeff : datumFourierCoeff (u t) a i ≠ 0),
    ProjectedForceSeparation T (Real.pi / 4) (localizedPairForce ν a β u F) :=
  @MethbokeAddon.FDSN.localizedPairForce_projectedSeparation

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairForce_projected_separates"
#check @MethbokeAddon.FDSN.localizedPairForce_projected_separates
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairForce_projected_separates"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairForce_projected_separates"
#print axioms MethbokeAddon.FDSN.localizedPairForce_projected_separates
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairForce_projected_separates"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairForce_projectedSeparation"
#check @MethbokeAddon.FDSN.localizedPairForce_projectedSeparation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairForce_projectedSeparation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairForce_projectedSeparation"
#print axioms MethbokeAddon.FDSN.localizedPairForce_projectedSeparation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairForce_projectedSeparation"

