import FDSNActiveTriad.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

open Set SingularClosure MethbokeAddon.FDSN
open scoped BigOperators ContDiff

noncomputable section

example {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) T)
    (htriad : ∀ t ∈ Ico a T,
      ¬ HasActiveNoncollinearTriad (datumFourierCoeff (u t))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico a T, ∀ k : Frequency, ∀ i : Fin 3,
      ‖datumFourierCoeff (u t) k i‖ ≤ C * (torusSobolevWeight k)⁻¹ ^ 4 :=
  Seed.uniform_fourier_envelope_of_no_active_triad h a ha htriad

example {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (s : ℝ) (hs : s ∈ Ico (0 : ℝ) T) :
    ∃ t ∈ Ioo s T, HasActiveNoncollinearTriad (datumFourierCoeff (u t)) :=
  Seed.exists_active_noncollinear_triad_after h s hs



end

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.Seed.uniform_fourier_envelope_of_no_active_triad"
#check @MethbokeAddon.FDSN.Seed.uniform_fourier_envelope_of_no_active_triad
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.Seed.uniform_fourier_envelope_of_no_active_triad"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.Seed.uniform_fourier_envelope_of_no_active_triad"
#print axioms MethbokeAddon.FDSN.Seed.uniform_fourier_envelope_of_no_active_triad
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.Seed.uniform_fourier_envelope_of_no_active_triad"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.Seed.exists_active_noncollinear_triad_after"
#check @MethbokeAddon.FDSN.Seed.exists_active_noncollinear_triad_after
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.Seed.exists_active_noncollinear_triad_after"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.Seed.exists_active_noncollinear_triad_after"
#print axioms MethbokeAddon.FDSN.Seed.exists_active_noncollinear_triad_after
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.Seed.exists_active_noncollinear_triad_after"

