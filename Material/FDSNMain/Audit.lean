import FDSNMain.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

open Set SingularClosure MethbokeAddon.FDSN
open scoped BigOperators ContDiff Topology

noncomputable section

example {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (h : Seed ν T u p F) (frame : HelicalFrameArray) :
    FamilyFor frame ν T u p F :=
  Seed.familyFor h frame

example
    (ν T : ℝ) (u : Velocity) (p : Pressure) (F : Velocity) :
    Seed ν T u p F → Family ν T u p F :=
  FEFFERMAN_D_SPECTRAL_NONRIGIDITY ν T u p F

example (ν T : ℝ) (u : Velocity) (p : Pressure) (F : Velocity) :
    Seed ν T u p F → Family ν T u p F :=
  FDSN ν T u p F

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (hseed : Seed ν T u p F)
    {frame : HelicalFrameArray} (hframe : IsHelicalFrame frame) :
    FamilyFor frame ν T u p F :=
  FEFFERMAN_D_SPECTRAL_NONRIGIDITY_fixed_frame hseed hframe





end

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.Seed.familyFor"
#check @MethbokeAddon.FDSN.Seed.familyFor
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.Seed.familyFor"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.Seed.familyFor"
#print axioms MethbokeAddon.FDSN.Seed.familyFor
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.Seed.familyFor"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY"
#check @MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY"
#print axioms MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.FDSN"
#check @MethbokeAddon.FDSN.FDSN
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.FDSN"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.FDSN"
#print axioms MethbokeAddon.FDSN.FDSN
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.FDSN"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY_fixed_frame"
#check @MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY_fixed_frame
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY_fixed_frame"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY_fixed_frame"
#print axioms MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY_fixed_frame
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.FEFFERMAN_D_SPECTRAL_NONRIGIDITY_fixed_frame"

