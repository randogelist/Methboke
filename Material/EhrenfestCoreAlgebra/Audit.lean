import EhrenfestCoreAlgebra.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-! Independently stated consumer types; fresh external evidence required. -/

open MethbokeAddon.EhrenfestObstruction

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

example : ∀ (b : E → E) (z g ψ : E → ℂ) (x : E),
    DifferentiableAt ℝ g x → DifferentiableAt ℝ ψ x →
      transportExpression b z (fun y => g y * ψ y) x -
        g x * transportExpression b z ψ x = fderiv ℝ g x (b x) * ψ x :=
  @transport_multiplication_commutator E _ _

example : ∀ (hbar : ℝ) (b : E → E) (z g ψ : E → ℂ) (x : E),
    DifferentiableAt ℝ g x → DifferentiableAt ℝ ψ x →
      hamiltonianExpression hbar b z (fun y => g y * ψ y) x -
        g x * hamiltonianExpression hbar b z ψ x =
          -Complex.I * (hbar : ℂ) * (fderiv ℝ g x (b x) * ψ x) :=
  @hamiltonian_multiplication_commutator E _ _

example : ∀ (hbar : ℝ), 0 < hbar →
    ∀ (b : E → E) (z g ψ : E → ℂ) (x : E),
      DifferentiableAt ℝ g x → DifferentiableAt ℝ ψ x →
        (Complex.I / (hbar : ℂ)) *
          (hamiltonianExpression hbar b z (fun y => g y * ψ y) x -
            g x * hamiltonianExpression hbar b z ψ x) =
          fderiv ℝ g x (b x) * ψ x :=
  @normalized_hamiltonian_commutator E _ _
end


#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.transport_multiplication_commutator"
#check @MethbokeAddon.EhrenfestObstruction.transport_multiplication_commutator
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.transport_multiplication_commutator"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.transport_multiplication_commutator"
#print axioms MethbokeAddon.EhrenfestObstruction.transport_multiplication_commutator
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.transport_multiplication_commutator"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.hamiltonian_multiplication_commutator"
#check @MethbokeAddon.EhrenfestObstruction.hamiltonian_multiplication_commutator
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.hamiltonian_multiplication_commutator"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.hamiltonian_multiplication_commutator"
#print axioms MethbokeAddon.EhrenfestObstruction.hamiltonian_multiplication_commutator
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.hamiltonian_multiplication_commutator"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.normalized_hamiltonian_commutator"
#check @MethbokeAddon.EhrenfestObstruction.normalized_hamiltonian_commutator
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.normalized_hamiltonian_commutator"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.normalized_hamiltonian_commutator"
#print axioms MethbokeAddon.EhrenfestObstruction.normalized_hamiltonian_commutator
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.normalized_hamiltonian_commutator"

