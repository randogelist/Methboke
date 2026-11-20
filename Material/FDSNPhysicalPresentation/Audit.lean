import FDSNPhysicalPresentation.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

open Set SingularClosure MethbokeAddon.FDSN
open scoped BigOperators ContDiff

noncomputable section

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (hseed : Seed ν T u p F)
    (frame : HelicalFrameArray) (s : ℝ) (hs : s ∈ Ico (0 : ℝ) T) :
    ∃ a b tstar ε : ℝ, ∃ U G : ℝ → Velocity,
      s < a ∧ a < b ∧ b < T ∧ tstar ∈ Ioo a b ∧ 0 < ε ∧
      U 0 = u ∧ G 0 = F ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
        (U q.1 - u) q.2.1 q.2.2) {q | |q.1| < ε} ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
        (G q.1 - F) q.2.1 q.2.2) {q | |q.1| < ε} ∧
      ExactRealizationAndAgreement ν T a b ε u p F U G ∧
      CompleteHelicalPowerPreservation frame T ε u U ∧
      TranslationSeparation tstar ε U ∧
      ProjectedForceSeparation T ε G ∧
      SmoothSmallness a b ε u F U G ∧
      (∀ lambda eta : ℝ, |lambda| < ε → |eta| < ε → lambda ≠ eta →
        ∃ t ∈ Ico (0 : ℝ) T, ∃ x : Vec,
          physicalLerayProjection ((G lambda - G eta) t) x ≠ 0) :=
  FEFFERMAN_D_SPECTRAL_NONRIGIDITY_physical hseed frame s hs


end

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY_physical"
#check @MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY_physical
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY_physical"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY_physical"
#print axioms MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY_physical
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY_physical"

