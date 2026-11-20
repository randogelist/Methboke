import FDSNCoefficientSmooth.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

open Set SingularClosure MethbokeAddon.FDSN MethbokeAddon.WeakFouriermanB
open scoped ContDiff

noncomputable section

example (n : ℕ) (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (k : Frequency) (i : Fin 3) :
    ContDiffOn ℝ n (fun t : ℝ => datumFourierCoeff (u t) k i) (Ioo (0 : ℝ) T) :=
  local_fourierCoeff_contDiffOn_nat n u T hu k i
example (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (k : Frequency) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun t : ℝ => datumFourierCoeff (u t) k i) (Ioo (0 : ℝ) T) :=
  local_fourierCoeff_contDiffOn u T hu k i
example {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (h : Seed ν T u p F) (k : Frequency) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun t : ℝ => datumFourierCoeff (u t) k i) (Ioo (0 : ℝ) T) :=
  h.fourierCoeff_contDiffOn k i
example {ν T a b : ℝ} {u F : Velocity} {p : Pressure}
    (h : Seed ν T u p F) (ha : 0 < a) (hb : b < T)
    (k : Frequency) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun t : ℝ => datumFourierCoeff (u t) k i) (Icc a b) :=
  h.fourierCoeff_contDiffOn_Icc ha hb k i


end

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.local_fourierCoeff_contDiffOn_nat"
#check @MethbokeAddon.FDSN.local_fourierCoeff_contDiffOn_nat
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.local_fourierCoeff_contDiffOn_nat"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.local_fourierCoeff_contDiffOn_nat"
#print axioms MethbokeAddon.FDSN.local_fourierCoeff_contDiffOn_nat
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.local_fourierCoeff_contDiffOn_nat"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.local_fourierCoeff_contDiffOn"
#check @MethbokeAddon.FDSN.local_fourierCoeff_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.local_fourierCoeff_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.local_fourierCoeff_contDiffOn"
#print axioms MethbokeAddon.FDSN.local_fourierCoeff_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.local_fourierCoeff_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.Seed.fourierCoeff_contDiffOn"
#check @MethbokeAddon.FDSN.Seed.fourierCoeff_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.Seed.fourierCoeff_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.Seed.fourierCoeff_contDiffOn"
#print axioms MethbokeAddon.FDSN.Seed.fourierCoeff_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.Seed.fourierCoeff_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.Seed.fourierCoeff_contDiffOn_Icc"
#check @MethbokeAddon.FDSN.Seed.fourierCoeff_contDiffOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.Seed.fourierCoeff_contDiffOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.Seed.fourierCoeff_contDiffOn_Icc"
#print axioms MethbokeAddon.FDSN.Seed.fourierCoeff_contDiffOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.Seed.fourierCoeff_contDiffOn_Icc"

