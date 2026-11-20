import FDSNFamilyRealization.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

open Set SingularClosure MethbokeAddon.FDSN
open scoped BigOperators ContDiff Topology

noncomputable section

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (k : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) (hβ0 : tsupport β ⊆ Ioo (0 : ℝ) T)
    (a b : ℝ) (hβI : tsupport β ⊆ Ioo a b) (λ : ℝ) :
    CompactTemporalCorrection a b (localizedPairVelocity k β u λ - u) :=
  localizedPairVelocity_compactCorrection h k hβ hβc hβ0 a b hβI λ

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (k : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) (hβ0 : tsupport β ⊆ Ioo (0 : ℝ) T)
    (a b : ℝ) (hβI : tsupport β ⊆ Ioo a b) (λ : ℝ) :
    CompactTemporalCorrection a b (localizedPairForce ν k β u F λ - F) :=
  localizedPairForce_compactCorrection h k hβ hβc hβ0 a b hβI λ

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (k : Frequency) {β : ℝ → ℝ} (a b : ℝ) (hbT : b < T)
    (hβI : tsupport β ⊆ Ioo a b) (λ : ℝ) :
    CofinalVelocityBlowup T (localizedPairVelocity k β u λ) :=
  localizedPairVelocity_terminal_blowup h k a b hbT hβI λ

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (frame : HelicalFrameArray) {k : Frequency} (hk : k ≠ 0)
    (β : ℝ → ℝ) (ε : ℝ) :
    CompleteHelicalPowerPreservation frame T ε u (localizedPairVelocity k β u) :=
  localizedPairVelocity_helicalPower h frame hk β ε

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (k : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : tsupport β ⊆ Ioo (0 : ℝ) T)
    (a b ε : ℝ) (hab : a ≤ b) :
    SmoothSmallness a b ε u F
      (localizedPairVelocity k β u) (localizedPairForce ν k β u F) :=
  localizedPair_family_smallness h k hβ hβ0 a b ε hab

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {k : Frequency} (hk : k ≠ 0) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) (hβ0 : tsupport β ⊆ Ioo (0 : ℝ) T)
    (a b ε : ℝ) (hbT : b < T) (hβI : tsupport β ⊆ Ioo a b) :
    ExactRealizationAndAgreement ν T a b ε u p F
      (localizedPairVelocity k β u) (localizedPairForce ν k β u F) :=
  localizedPair_exactRealization h hk hβ hβc hβ0 a b ε hbT hβI







end

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_compactCorrection"
#check @MethbokeAddon.FDSN.localizedPairVelocity_compactCorrection
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_compactCorrection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_compactCorrection"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_compactCorrection
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_compactCorrection"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairForce_compactCorrection"
#check @MethbokeAddon.FDSN.localizedPairForce_compactCorrection
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairForce_compactCorrection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairForce_compactCorrection"
#print axioms MethbokeAddon.FDSN.localizedPairForce_compactCorrection
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairForce_compactCorrection"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_terminal_blowup"
#check @MethbokeAddon.FDSN.localizedPairVelocity_terminal_blowup
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_terminal_blowup"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_terminal_blowup"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_terminal_blowup
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_terminal_blowup"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_helicalPower"
#check @MethbokeAddon.FDSN.localizedPairVelocity_helicalPower
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_helicalPower"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_helicalPower"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_helicalPower
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_helicalPower"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPair_family_smallness"
#check @MethbokeAddon.FDSN.localizedPair_family_smallness
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPair_family_smallness"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPair_family_smallness"
#print axioms MethbokeAddon.FDSN.localizedPair_family_smallness
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPair_family_smallness"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPair_exactRealization"
#check @MethbokeAddon.FDSN.localizedPair_exactRealization
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPair_exactRealization"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPair_exactRealization"
#print axioms MethbokeAddon.FDSN.localizedPair_exactRealization
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPair_exactRealization"

