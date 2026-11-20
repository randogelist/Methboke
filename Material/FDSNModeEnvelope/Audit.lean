import FDSNModeEnvelope.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

open Set Filter SingularClosure MethbokeAddon.FDSN
open scoped BigOperators Topology

noncomputable section

example {E : ℝ → ℝ} {a T A G ρ : ℝ}
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hρ : 0 ≤ ρ)
    (hd : ∀ r ∈ Ico a T, DifferentiableAt ℝ E r)
    (hinit : E a ≤ A * ρ)
    (hbound : ∀ r ∈ Ico a T, deriv E r ≤ E r + G * ρ)
    (t : ℝ) (ht : t ∈ Ico a T) :
    E t ≤ ((A + G) * Real.exp (T - a)) * ρ :=
  uniform_energy_bound_of_deriv_le hA hG hρ hd hinit hbound t ht

example {z : ℂ} {C r : ℝ}
    (h : ‖z‖ ≤ C * r ^ 4) : Complex.normSq z ≤ C ^ 2 * r ^ 8 :=
  complex_normSq_le_of_weighted_norm_le h

example (k : Frequency) (v : Fin 3 → ℂ) (C : ℝ)
    (hv : ∀ j : Fin 3, ‖v j‖ ≤ C * (torusSobolevWeight k)⁻¹ ^ 4)
    (i : Fin 3) :
    Complex.normSq (coefficientLeray k v i) ≤
      (3 * C ^ 2) * (torusSobolevWeight k)⁻¹ ^ 8 :=
  coefficientLeray_component_normSq_le_envelope k v C hv i

example {z : ℂ} {B r : ℝ}
    (hB : 0 ≤ B) (h : Complex.normSq z ≤ B * r ^ 8) :
    ‖z‖ ≤ Real.sqrt B * r ^ 4 :=
  weighted_norm_le_of_normSq_le hB h





end

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.uniform_energy_bound_of_deriv_le"
#check @MethbokeAddon.FDSN.uniform_energy_bound_of_deriv_le
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.uniform_energy_bound_of_deriv_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.uniform_energy_bound_of_deriv_le"
#print axioms MethbokeAddon.FDSN.uniform_energy_bound_of_deriv_le
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.uniform_energy_bound_of_deriv_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.complex_normSq_le_of_weighted_norm_le"
#check @MethbokeAddon.FDSN.complex_normSq_le_of_weighted_norm_le
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.complex_normSq_le_of_weighted_norm_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.complex_normSq_le_of_weighted_norm_le"
#print axioms MethbokeAddon.FDSN.complex_normSq_le_of_weighted_norm_le
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.complex_normSq_le_of_weighted_norm_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.coefficientLeray_component_normSq_le_envelope"
#check @MethbokeAddon.FDSN.coefficientLeray_component_normSq_le_envelope
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.coefficientLeray_component_normSq_le_envelope"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.coefficientLeray_component_normSq_le_envelope"
#print axioms MethbokeAddon.FDSN.coefficientLeray_component_normSq_le_envelope
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.coefficientLeray_component_normSq_le_envelope"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.weighted_norm_le_of_normSq_le"
#check @MethbokeAddon.FDSN.weighted_norm_le_of_normSq_le
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.weighted_norm_le_of_normSq_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.weighted_norm_le_of_normSq_le"
#print axioms MethbokeAddon.FDSN.weighted_norm_le_of_normSq_le
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.weighted_norm_le_of_normSq_le"

