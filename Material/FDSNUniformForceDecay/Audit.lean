import FDSNUniformForceDecay.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory SingularClosure MethbokeAddon.FDSN
open MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff

noncomputable section

/- Complete literal consumer types. -/

example
    (j : Fin 3) (m : ℕ) (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime S)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec =>
      iteratedCoordinateDerivative j m (u z.1) z.2) (initialFrontSpacetime S) :=
  initial_iteratedCoordinateDerivative_contDiffOn j m u S hu

example
    (j : Fin 3) (m : ℕ) (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime S))
    (i : Fin 3) (τ : ℝ) (hτS : τ < S) :
    ContinuousOn (fun t => coordinateDerivativeL1 j m (u t) i) (Icc (0 : ℝ) τ) :=
  initial_coordinateDerivativeL1_continuousOn_Icc j m u S hu i τ hτS

example
    (m : ℕ) (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime S))
    (τ : ℝ) (hτS : τ < S) :
    ContinuousOn (fun t => fourierDecayConstant m (u t)) (Icc (0 : ℝ) τ) :=
  initial_fourierDecayConstant_continuousOn_Icc m u S hu τ hτS

example
    (s : ℕ) (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime S))
    (τ : ℝ) (hτS : τ < S) :
    ContinuousOn (fun t => smoothDatumDecayConstant s (u t)) (Icc (0 : ℝ) τ) :=
  initial_smoothDatumDecayConstant_continuousOn_Icc s u S hu τ hτS

example {F : Velocity}
    (hF : MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce F)
    (T : ℝ) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Frequency, ∀ i : Fin 3,
      torusSobolevWeight k ^ (s + 2) * ‖datumFourierCoeff (F t) k i‖ ≤ C :=
  admissibleForce_uniform_fourier_weight_bound hF T s

example {F : Velocity}
    (hF : MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce F) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Frequency, ∀ i : Fin 3,
      ‖datumFourierCoeff (F t) k i‖ ≤ C * (torusSobolevWeight k)⁻¹ ^ 4 :=
  admissibleForce_uniform_fourier_envelope hF T







end

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.initial_iteratedCoordinateDerivative_contDiffOn"
#check @MethbokeAddon.FDSN.initial_iteratedCoordinateDerivative_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.initial_iteratedCoordinateDerivative_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.initial_iteratedCoordinateDerivative_contDiffOn"
#print axioms MethbokeAddon.FDSN.initial_iteratedCoordinateDerivative_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.initial_iteratedCoordinateDerivative_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.initial_coordinateDerivativeL1_continuousOn_Icc"
#check @MethbokeAddon.FDSN.initial_coordinateDerivativeL1_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.initial_coordinateDerivativeL1_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.initial_coordinateDerivativeL1_continuousOn_Icc"
#print axioms MethbokeAddon.FDSN.initial_coordinateDerivativeL1_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.initial_coordinateDerivativeL1_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.initial_fourierDecayConstant_continuousOn_Icc"
#check @MethbokeAddon.FDSN.initial_fourierDecayConstant_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.initial_fourierDecayConstant_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.initial_fourierDecayConstant_continuousOn_Icc"
#print axioms MethbokeAddon.FDSN.initial_fourierDecayConstant_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.initial_fourierDecayConstant_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.initial_smoothDatumDecayConstant_continuousOn_Icc"
#check @MethbokeAddon.FDSN.initial_smoothDatumDecayConstant_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.initial_smoothDatumDecayConstant_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.initial_smoothDatumDecayConstant_continuousOn_Icc"
#print axioms MethbokeAddon.FDSN.initial_smoothDatumDecayConstant_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.initial_smoothDatumDecayConstant_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.admissibleForce_uniform_fourier_weight_bound"
#check @MethbokeAddon.FDSN.admissibleForce_uniform_fourier_weight_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.admissibleForce_uniform_fourier_weight_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.admissibleForce_uniform_fourier_weight_bound"
#print axioms MethbokeAddon.FDSN.admissibleForce_uniform_fourier_weight_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.admissibleForce_uniform_fourier_weight_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.admissibleForce_uniform_fourier_envelope"
#check @MethbokeAddon.FDSN.admissibleForce_uniform_fourier_envelope
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.admissibleForce_uniform_fourier_envelope"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.admissibleForce_uniform_fourier_envelope"
#print axioms MethbokeAddon.FDSN.admissibleForce_uniform_fourier_envelope
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.admissibleForce_uniform_fourier_envelope"

