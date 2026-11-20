import FDSNR3CompactSchwartz.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open Set SingularClosure MethbokeAddon.FDSNR3
open scoped ContDiff Topology

example (T : ℝ) :
    UniqueDiffOn ℝ (preterminalSpacetime T) :=
  uniqueDiffOn_preterminalSpacetime T

example {T : ℝ} {u : Velocity} {K : Set Vec} (hK : IsClosed K)
    (hcarrier : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, x ∉ K → u t x = 0)
    (n : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    {x : Vec} (hx : x ∉ K) :
    iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T) (t, x) = 0 :=
  iteratedFDerivWithin_eq_zero_off_spatialCarrier hK hcarrier n ht hx

example {T : ℝ} {u : Velocity} {K : Set Vec} (hK : IsClosed K)
    (hcarrier : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, x ∉ K → u t x = 0)
    (N n : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    {x : Vec} (hx : x ∉ K) :
    weightedJetWithin T N n u (t, x) = 0 :=
  weightedJetWithin_eq_zero_off_spatialCarrier hK hcarrier N n ht hx

example {T : ℝ} {u : Velocity} {K : Set Vec} (hK : IsCompact K)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T))
    (hcarrier : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, x ∉ K → u t x = 0) :
    LocalSchwartz T u :=
  localSchwartz_of_compact_spatialCarrier hK hu hcarrier

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.uniqueDiffOn_preterminalSpacetime"
#check @MethbokeAddon.FDSNR3.uniqueDiffOn_preterminalSpacetime
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.uniqueDiffOn_preterminalSpacetime"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.uniqueDiffOn_preterminalSpacetime"
#print axioms MethbokeAddon.FDSNR3.uniqueDiffOn_preterminalSpacetime
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.uniqueDiffOn_preterminalSpacetime"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.iteratedFDerivWithin_eq_zero_off_spatialCarrier"
#check @MethbokeAddon.FDSNR3.iteratedFDerivWithin_eq_zero_off_spatialCarrier
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.iteratedFDerivWithin_eq_zero_off_spatialCarrier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.iteratedFDerivWithin_eq_zero_off_spatialCarrier"
#print axioms MethbokeAddon.FDSNR3.iteratedFDerivWithin_eq_zero_off_spatialCarrier
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.iteratedFDerivWithin_eq_zero_off_spatialCarrier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.weightedJetWithin_eq_zero_off_spatialCarrier"
#check @MethbokeAddon.FDSNR3.weightedJetWithin_eq_zero_off_spatialCarrier
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.weightedJetWithin_eq_zero_off_spatialCarrier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.weightedJetWithin_eq_zero_off_spatialCarrier"
#print axioms MethbokeAddon.FDSNR3.weightedJetWithin_eq_zero_off_spatialCarrier
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.weightedJetWithin_eq_zero_off_spatialCarrier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.localSchwartz_of_compact_spatialCarrier"
#check @MethbokeAddon.FDSNR3.localSchwartz_of_compact_spatialCarrier
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.localSchwartz_of_compact_spatialCarrier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.localSchwartz_of_compact_spatialCarrier"
#print axioms MethbokeAddon.FDSNR3.localSchwartz_of_compact_spatialCarrier
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.localSchwartz_of_compact_spatialCarrier"

