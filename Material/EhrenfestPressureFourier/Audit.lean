import EhrenfestPressureFourier.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-! Independent exact consumer types; external evidence pending. -/


section Consumer1
/-! Exact consumer propositions and axiom queries for external verification. -/

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff

namespace MethbokeAddon.EhrenfestObstruction.PressureTypeChecks

example :
    ∀ (p : Vec → ℝ) (x : Vec),
      MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent p x 0 = p x :=
  @MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_apply_zero

example :
    ∀ (p : Vec → ℝ), ContDiff ℝ ∞ p →
      ContDiff ℝ ∞ (MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent p) :=
  @MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_contDiff

example :
    ∀ (p : Vec → ℝ), SpatialPeriodic p →
      SpatialPeriodic (MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent p) :=
  @MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_periodic

example :
    ∀ (p : Vec → ℝ), ContDiff ℝ ∞ p → ∀ k : Frequency,
      IntegrableOn (fun x : Vec => star (fourierCharacter k x) * (p x : ℂ))
        unitCube volume :=
  @MethbokeAddon.EhrenfestObstruction.scalarPressureFourierIntegrand_integrableOn

example :
    ∀ (p : Vec → ℝ) (k : Frequency),
      datumFourierCoeff (MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent p) k 0 =
        MethbokeAddon.EhrenfestObstruction.scalarPressureFourierCoeff p k :=
  @MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_pressureAsFirstComponent_zero

example :
    ∀ (p : Vec → ℝ), ContDiff ℝ ∞ p → ∀ (j : Fin 3) (x : Vec),
      coordinateDerivative (MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent p) j x 0 =
        fderiv ℝ p x (unitVector j) :=
  @MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_coordinateDerivative_zero

example :
    ∀ (p : Vec → ℝ), ContDiff ℝ ∞ p → SpatialPeriodic p →
      datumFourierCoeff (SingularClosure.gradient p) =
        fun k i => derivativeSymbol i k *
          MethbokeAddon.EhrenfestObstruction.scalarPressureFourierCoeff p k :=
  @MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_gradient

example :
    ∀ (k : Frequency) (z : ℂ),
      coefficientLeray k (fun i => (k i : ℂ) * z) = 0 :=
  @MethbokeAddon.EhrenfestObstruction.coefficientLeray_frequency_mul_eq_zero

example :
    ∀ (k : Frequency) (z : ℂ),
      coefficientLeray k (fun i => derivativeSymbol i k * z) = 0 :=
  @MethbokeAddon.EhrenfestObstruction.coefficientLeray_derivativeSymbol_mul_eq_zero

example :
    ∀ (p : Vec → ℝ), ContDiff ℝ ∞ p → SpatialPeriodic p → ∀ k : Frequency,
      coefficientLeray k (datumFourierCoeff (SingularClosure.gradient p) k) = 0 :=
  @MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_gradient_leray_eq_zero

end MethbokeAddon.EhrenfestObstruction.PressureTypeChecks
end Consumer1


#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_apply_zero"
#check @MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_apply_zero
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_apply_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_apply_zero"
#print axioms MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_apply_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_apply_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_contDiff"
#check @MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_contDiff
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_contDiff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_contDiff"
#print axioms MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_contDiff
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_contDiff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_periodic"
#check @MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_periodic
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_periodic"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_periodic"
#print axioms MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_periodic
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_periodic"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.scalarPressureFourierIntegrand_integrableOn"
#check @MethbokeAddon.EhrenfestObstruction.scalarPressureFourierIntegrand_integrableOn
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.scalarPressureFourierIntegrand_integrableOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.scalarPressureFourierIntegrand_integrableOn"
#print axioms MethbokeAddon.EhrenfestObstruction.scalarPressureFourierIntegrand_integrableOn
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.scalarPressureFourierIntegrand_integrableOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_pressureAsFirstComponent_zero"
#check @MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_pressureAsFirstComponent_zero
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_pressureAsFirstComponent_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_pressureAsFirstComponent_zero"
#print axioms MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_pressureAsFirstComponent_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_pressureAsFirstComponent_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_coordinateDerivative_zero"
#check @MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_coordinateDerivative_zero
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_coordinateDerivative_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_coordinateDerivative_zero"
#print axioms MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_coordinateDerivative_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.pressureAsFirstComponent_coordinateDerivative_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_gradient"
#check @MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_gradient
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_gradient"
#print axioms MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficientLeray_frequency_mul_eq_zero"
#check @MethbokeAddon.EhrenfestObstruction.coefficientLeray_frequency_mul_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.coefficientLeray_frequency_mul_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficientLeray_frequency_mul_eq_zero"
#print axioms MethbokeAddon.EhrenfestObstruction.coefficientLeray_frequency_mul_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.coefficientLeray_frequency_mul_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficientLeray_derivativeSymbol_mul_eq_zero"
#check @MethbokeAddon.EhrenfestObstruction.coefficientLeray_derivativeSymbol_mul_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.coefficientLeray_derivativeSymbol_mul_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficientLeray_derivativeSymbol_mul_eq_zero"
#print axioms MethbokeAddon.EhrenfestObstruction.coefficientLeray_derivativeSymbol_mul_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.coefficientLeray_derivativeSymbol_mul_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_gradient_leray_eq_zero"
#check @MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_gradient_leray_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_gradient_leray_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_gradient_leray_eq_zero"
#print axioms MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_gradient_leray_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_gradient_leray_eq_zero"
