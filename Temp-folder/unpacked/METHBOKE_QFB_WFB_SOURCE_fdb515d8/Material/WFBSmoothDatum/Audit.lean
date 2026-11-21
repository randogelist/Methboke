import WFBSmoothDatum.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB MethbokeAddon.WeakFouriermanB
open scoped ContDiff ENNReal Topology

-- Exact Q01 input adapter: no additional existence/regularity premise.
example : ∀ (ν : ℝ), 0 < ν → ∀ (a : Field), SmoothSigmaZero a →
    ∃ (u : Velocity) (G : WeakGradientTrajectory),
      CriticalLerayHopf ν (criticalL2Representative a) u G ∧
      u 0 =ᵐ[volume.restrict unitCube] a :=
  @smooth_datum_lerayHopf_exists

-- Literal cutoff normalization is checked independently of its proof body.
example : ∀ {a : Field}, SmoothSigmaZero a → ∀ (ν : ℝ),
    cutoff (criticalL2Representative a) ν =
      (physicalEnergy a) ^ 2 / (8 * Real.pi ^ 2 * ν ^ 5) :=
  @smooth_datum_cutoff

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_memLp"
#check @MethbokeAddon.WeakFouriermanB.smooth_datum_memLp
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.smooth_datum_memLp"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_memLp"
#print axioms MethbokeAddon.WeakFouriermanB.smooth_datum_memLp
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.smooth_datum_memLp"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_representative_ae"
#check @MethbokeAddon.WeakFouriermanB.smooth_datum_representative_ae
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.smooth_datum_representative_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_representative_ae"
#print axioms MethbokeAddon.WeakFouriermanB.smooth_datum_representative_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.smooth_datum_representative_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_constant_pairing_zero"
#check @MethbokeAddon.WeakFouriermanB.smooth_datum_constant_pairing_zero
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.smooth_datum_constant_pairing_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_constant_pairing_zero"
#print axioms MethbokeAddon.WeakFouriermanB.smooth_datum_constant_pairing_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.smooth_datum_constant_pairing_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_energySigmaZero"
#check @MethbokeAddon.WeakFouriermanB.smooth_datum_energySigmaZero
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.smooth_datum_energySigmaZero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_energySigmaZero"
#print axioms MethbokeAddon.WeakFouriermanB.smooth_datum_energySigmaZero
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.smooth_datum_energySigmaZero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_representative_norm_sq"
#check @MethbokeAddon.WeakFouriermanB.smooth_datum_representative_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.smooth_datum_representative_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_representative_norm_sq"
#print axioms MethbokeAddon.WeakFouriermanB.smooth_datum_representative_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.smooth_datum_representative_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_cutoff"
#check @MethbokeAddon.WeakFouriermanB.smooth_datum_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.smooth_datum_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_cutoff"
#print axioms MethbokeAddon.WeakFouriermanB.smooth_datum_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.smooth_datum_cutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_lerayHopf_exists"
#check @MethbokeAddon.WeakFouriermanB.smooth_datum_lerayHopf_exists
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.smooth_datum_lerayHopf_exists"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.smooth_datum_lerayHopf_exists"
#print axioms MethbokeAddon.WeakFouriermanB.smooth_datum_lerayHopf_exists
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.smooth_datum_lerayHopf_exists"

