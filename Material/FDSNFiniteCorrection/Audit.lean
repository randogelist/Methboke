import FDSNFiniteCorrection.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory
open scoped BigOperators ContDiff
open SingularClosure MethbokeAddon.FDSN

noncomputable section

example {a : Frequency} (ha : a ≠ 0) (z : ℂ) (c : FourierCoeff) (i : Fin 3)
    (hc : Summable (fun k => ‖c k i‖)) (x : Vec) :
    scalarFourierSeries (fun k => pairRotate a z c k i) x =
      scalarFourierSeries (fun k => c k i) x +
        fourierCharacter a x * ((z - 1) * c a i) +
        fourierCharacter (-a) x * ((star z - 1) * c (-a) i) :=
  scalarFourierSeries_pairRotate ha z c i hc x
example : Frequency → ℂ → Field → Field := physicalPairCorrection
example (a : Frequency) (z : ℂ) (v : Field) (x : Vec) (i : Fin 3) :
    physicalPairCorrection a z v x i =
      2 * (fourierCharacter a x * ((z - 1) * datumFourierCoeff v a i)).re := rfl
example (a : Frequency) (v : Field) : physicalPairCorrection a 1 v = 0 :=
  physicalPairCorrection_one a v
example (a : Frequency) (z : ℂ) (v : Field) :
    ContDiff ℝ ∞ (physicalPairCorrection a z v) := physicalPairCorrection_smooth a z v
example (a : Frequency) (z : ℂ) (v : Field) :
    SpatialPeriodic (physicalPairCorrection a z v) := physicalPairCorrection_periodic a z v
example {a : Frequency} (ha : a ≠ 0) (z : ℂ) {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    physicalPairRotation a z v = v + physicalPairCorrection a z v :=
  physicalPairRotation_eq_add_correction ha z hv hp
example {a : Frequency} (ha : a ≠ 0) (z : ℂ) {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    physicalPairRotation a z v - v = physicalPairCorrection a z v :=
  PHYSICAL_PAIR_ROTATION_IS_FINITE_CORRECTION ha z hv hp


end

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.scalarFourierSeries_pairRotate"
#check @MethbokeAddon.FDSN.scalarFourierSeries_pairRotate
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.scalarFourierSeries_pairRotate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.scalarFourierSeries_pairRotate"
#print axioms MethbokeAddon.FDSN.scalarFourierSeries_pairRotate
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.scalarFourierSeries_pairRotate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalPairCorrection"
#check @MethbokeAddon.FDSN.physicalPairCorrection
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalPairCorrection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalPairCorrection"
#print axioms MethbokeAddon.FDSN.physicalPairCorrection
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalPairCorrection"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalPairCorrection_one"
#check @MethbokeAddon.FDSN.physicalPairCorrection_one
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalPairCorrection_one"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalPairCorrection_one"
#print axioms MethbokeAddon.FDSN.physicalPairCorrection_one
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalPairCorrection_one"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalPairCorrection_smooth"
#check @MethbokeAddon.FDSN.physicalPairCorrection_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalPairCorrection_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalPairCorrection_smooth"
#print axioms MethbokeAddon.FDSN.physicalPairCorrection_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalPairCorrection_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalPairCorrection_periodic"
#check @MethbokeAddon.FDSN.physicalPairCorrection_periodic
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalPairCorrection_periodic"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalPairCorrection_periodic"
#print axioms MethbokeAddon.FDSN.physicalPairCorrection_periodic
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalPairCorrection_periodic"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_eq_add_correction"
#check @MethbokeAddon.FDSN.physicalPairRotation_eq_add_correction
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalPairRotation_eq_add_correction"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalPairRotation_eq_add_correction"
#print axioms MethbokeAddon.FDSN.physicalPairRotation_eq_add_correction
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalPairRotation_eq_add_correction"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PHYSICAL_PAIR_ROTATION_IS_FINITE_CORRECTION"
#check @MethbokeAddon.FDSN.PHYSICAL_PAIR_ROTATION_IS_FINITE_CORRECTION
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PHYSICAL_PAIR_ROTATION_IS_FINITE_CORRECTION"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PHYSICAL_PAIR_ROTATION_IS_FINITE_CORRECTION"
#print axioms MethbokeAddon.FDSN.PHYSICAL_PAIR_ROTATION_IS_FINITE_CORRECTION
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PHYSICAL_PAIR_ROTATION_IS_FINITE_CORRECTION"

