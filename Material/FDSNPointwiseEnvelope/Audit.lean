import FDSNPointwiseEnvelope.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

open Set SingularClosure MethbokeAddon.FDSN
open scoped BigOperators ContDiff

noncomputable section

example : ℝ :=
  torusEnvelopeMass

example : 0 ≤ torusEnvelopeMass :=
  torusEnvelopeMass_nonneg

example {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Frequency, ∀ i : Fin 3,
      ‖datumFourierCoeff v k i‖ ≤ C * (torusSobolevWeight k)⁻¹ ^ 4 :=
  smoothPeriodic_exists_fourier_envelope hv hp

example {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (C : ℝ)
    (hc : ∀ k : Frequency, ∀ i : Fin 3,
      ‖datumFourierCoeff v k i‖ ≤ C * (torusSobolevWeight k)⁻¹ ^ 4)
    (x : Vec) (i : Fin 3) : ‖v x i‖ ≤ C * torusEnvelopeMass :=
  component_bound_of_fourier_envelope hv hp C hc x i

example {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ k : Frequency, ∀ i : Fin 3,
      ‖datumFourierCoeff v k i‖ ≤ C * (torusSobolevWeight k)⁻¹ ^ 4)
    (x : Vec) : ‖v x‖ ≤ 3 * (C * torusEnvelopeMass) :=
  pointwise_bound_of_fourier_envelope hv hp hC hc x

example {ν T : ℝ} {u F : Velocity}
    {p : Pressure} (h : Seed ν T u p F) (s : ℝ) (hs : s ∈ Ico (0 : ℝ) T) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo s T, ∀ k : Frequency, ∀ i : Fin 3,
      ‖datumFourierCoeff (u t) k i‖ ≤ C * (torusSobolevWeight k)⁻¹ ^ 4 :=
  Seed.no_final_uniform_fourier_envelope h s hs

example : torusEnvelopeMass = ∑' k : Frequency, (torusSobolevWeight k)⁻¹ ^ 4 := rfl







end

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.torusEnvelopeMass"
#check @MethbokeAddon.FDSN.torusEnvelopeMass
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.torusEnvelopeMass"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.torusEnvelopeMass"
#print axioms MethbokeAddon.FDSN.torusEnvelopeMass
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.torusEnvelopeMass"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.torusEnvelopeMass_nonneg"
#check @MethbokeAddon.FDSN.torusEnvelopeMass_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.torusEnvelopeMass_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.torusEnvelopeMass_nonneg"
#print axioms MethbokeAddon.FDSN.torusEnvelopeMass_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.torusEnvelopeMass_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.smoothPeriodic_exists_fourier_envelope"
#check @MethbokeAddon.FDSN.smoothPeriodic_exists_fourier_envelope
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.smoothPeriodic_exists_fourier_envelope"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.smoothPeriodic_exists_fourier_envelope"
#print axioms MethbokeAddon.FDSN.smoothPeriodic_exists_fourier_envelope
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.smoothPeriodic_exists_fourier_envelope"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.component_bound_of_fourier_envelope"
#check @MethbokeAddon.FDSN.component_bound_of_fourier_envelope
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.component_bound_of_fourier_envelope"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.component_bound_of_fourier_envelope"
#print axioms MethbokeAddon.FDSN.component_bound_of_fourier_envelope
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.component_bound_of_fourier_envelope"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pointwise_bound_of_fourier_envelope"
#check @MethbokeAddon.FDSN.pointwise_bound_of_fourier_envelope
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pointwise_bound_of_fourier_envelope"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pointwise_bound_of_fourier_envelope"
#print axioms MethbokeAddon.FDSN.pointwise_bound_of_fourier_envelope
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pointwise_bound_of_fourier_envelope"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.Seed.no_final_uniform_fourier_envelope"
#check @MethbokeAddon.FDSN.Seed.no_final_uniform_fourier_envelope
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.Seed.no_final_uniform_fourier_envelope"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.Seed.no_final_uniform_fourier_envelope"
#print axioms MethbokeAddon.FDSN.Seed.no_final_uniform_fourier_envelope
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.Seed.no_final_uniform_fourier_envelope"

