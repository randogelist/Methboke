import WFBPhysicalNonlinear.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff ENNReal NNReal RealInnerProductSpace
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.physicalLaplacianSquare_nonneg
example : ∀ (v : Field),
    0 ≤ physicalLaplacianSquare v :=
  @MethbokeAddon.WeakFouriermanB.physicalLaplacianSquare_nonneg

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.physical_dissipation_nonneg
example : ∀ (v : Field),
    0 ≤ physicalDissipation v :=
  @MethbokeAddon.WeakFouriermanB.physical_dissipation_nonneg

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.physical_laplacian_coordinateDerivative_commute
example : ∀ (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (i : Fin 3),
    laplacian (coordinateDerivative v i) = coordinateDerivative (laplacian v) i :=
  @MethbokeAddon.WeakFouriermanB.physical_laplacian_coordinateDerivative_commute

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.physical_coordinateDerivative_meanZero
example : ∀ (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (i : Fin 3),
    MeanZero (coordinateDerivative v i) :=
  @MethbokeAddon.WeakFouriermanB.physical_coordinateDerivative_meanZero

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.physical_hessian_laplacian_eq
example : ∀ (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v),
    (∑ i : Fin 3, physicalDissipation (coordinateDerivative v i)) =
      physicalLaplacianSquare v :=
  @MethbokeAddon.WeakFouriermanB.physical_hessian_laplacian_eq

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.physical_coordinateDissipation_le_laplacianSquare
example : ∀ (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (i : Fin 3),
    physicalDissipation (coordinateDerivative v i) ≤ physicalLaplacianSquare v :=
  @MethbokeAddon.WeakFouriermanB.physical_coordinateDissipation_le_laplacianSquare

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.physical_fderiv_eLpNorm_two_le
example : ∀ (v : Field) (hv : ContDiff ℝ ∞ v),
    eLpNorm (fderiv ℝ v) 2 (volume.restrict unitCube) ≤
      (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (physicalDissipation v)) ^ (1 / 2 : ℝ) :=
  @MethbokeAddon.WeakFouriermanB.physical_fderiv_eLpNorm_two_le

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.physical_eLpNorm_two_le_dissipation
example : ∀ (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (hz : MeanZero v),
    eLpNorm v 2 (volume.restrict unitCube) ≤
      (ENNReal.ofReal (physicalDissipation v)) ^ (1 / 2 : ℝ) :=
  @MethbokeAddon.WeakFouriermanB.physical_eLpNorm_two_le_dissipation

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.physical_laplacian_eLpNorm_two
example : ∀ (v : Field) (hv : ContDiff ℝ ∞ v),
    eLpNorm (laplacian v) 2 (volume.restrict unitCube) =
      (ENNReal.ofReal (physicalLaplacianSquare v)) ^ (1 / 2 : ℝ) :=
  @MethbokeAddon.WeakFouriermanB.physical_laplacian_eLpNorm_two

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.PHYSICAL_L6_FROM_DISSIPATION
example : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ v : Field, ContDiff ℝ ∞ v → SpatialPeriodic v →
      MeanZero v → eLpNorm v 6 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (physicalDissipation v)) ^ (1 / 2 : ℝ) :=
  @MethbokeAddon.WeakFouriermanB.PHYSICAL_L6_FROM_DISSIPATION

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.PHYSICAL_DERIVATIVE_L6_FROM_LAPLACIAN
example : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ v : Field, ContDiff ℝ ∞ v → SpatialPeriodic v →
      eLpNorm (fderiv ℝ v) 6 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (physicalLaplacianSquare v)) ^ (1 / 2 : ℝ) :=
  @MethbokeAddon.WeakFouriermanB.PHYSICAL_DERIVATIVE_L6_FROM_LAPLACIAN

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_THREE_QUARTER_BOUND
example : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ v : Field, ContDiff ℝ ∞ v → SpatialPeriodic v →
      MeanZero v → ENNReal.ofReal (abs (∫ x in unitCube,
        inner ℝ (convection v x) (laplacian v x))) ≤
          C * (ENNReal.ofReal (physicalDissipation v)) ^ (3 / 4 : ℝ) *
            (ENNReal.ofReal (physicalLaplacianSquare v)) ^ (3 / 4 : ℝ) :=
  @MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_THREE_QUARTER_BOUND

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_REAL_BOUND
example : ∃ K : ℝ, 0 ≤ K ∧ ∀ v : Field, ContDiff ℝ ∞ v → SpatialPeriodic v →
      MeanZero v → abs (∫ x in unitCube,
        inner ℝ (convection v x) (laplacian v x)) ≤
          K * (physicalDissipation v) ^ (3 / 4 : ℝ) *
            (physicalLaplacianSquare v) ^ (3 / 4 : ℝ) :=
  @MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_REAL_BOUND

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_ABSORPTION
example : ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ v : Field,
      ContDiff ℝ ∞ v → SpatialPeriodic v → MeanZero v →
      2 * (∫ x in unitCube, inner ℝ (convection v x) (laplacian v x)) ≤
        ν * physicalLaplacianSquare v + C / ν ^ 3 * physicalDissipation v ^ 3 :=
  @MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_ABSORPTION

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physicalLaplacianSquare_nonneg"
#check @MethbokeAddon.WeakFouriermanB.physicalLaplacianSquare_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physicalLaplacianSquare_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physicalLaplacianSquare_nonneg"
#print axioms MethbokeAddon.WeakFouriermanB.physicalLaplacianSquare_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physicalLaplacianSquare_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physical_dissipation_nonneg"
#check @MethbokeAddon.WeakFouriermanB.physical_dissipation_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physical_dissipation_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physical_dissipation_nonneg"
#print axioms MethbokeAddon.WeakFouriermanB.physical_dissipation_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physical_dissipation_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physical_laplacian_coordinateDerivative_commute"
#check @MethbokeAddon.WeakFouriermanB.physical_laplacian_coordinateDerivative_commute
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physical_laplacian_coordinateDerivative_commute"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physical_laplacian_coordinateDerivative_commute"
#print axioms MethbokeAddon.WeakFouriermanB.physical_laplacian_coordinateDerivative_commute
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physical_laplacian_coordinateDerivative_commute"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physical_coordinateDerivative_meanZero"
#check @MethbokeAddon.WeakFouriermanB.physical_coordinateDerivative_meanZero
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physical_coordinateDerivative_meanZero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physical_coordinateDerivative_meanZero"
#print axioms MethbokeAddon.WeakFouriermanB.physical_coordinateDerivative_meanZero
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physical_coordinateDerivative_meanZero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physical_hessian_laplacian_eq"
#check @MethbokeAddon.WeakFouriermanB.physical_hessian_laplacian_eq
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physical_hessian_laplacian_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physical_hessian_laplacian_eq"
#print axioms MethbokeAddon.WeakFouriermanB.physical_hessian_laplacian_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physical_hessian_laplacian_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physical_coordinateDissipation_le_laplacianSquare"
#check @MethbokeAddon.WeakFouriermanB.physical_coordinateDissipation_le_laplacianSquare
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physical_coordinateDissipation_le_laplacianSquare"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physical_coordinateDissipation_le_laplacianSquare"
#print axioms MethbokeAddon.WeakFouriermanB.physical_coordinateDissipation_le_laplacianSquare
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physical_coordinateDissipation_le_laplacianSquare"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physical_fderiv_eLpNorm_two_le"
#check @MethbokeAddon.WeakFouriermanB.physical_fderiv_eLpNorm_two_le
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physical_fderiv_eLpNorm_two_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physical_fderiv_eLpNorm_two_le"
#print axioms MethbokeAddon.WeakFouriermanB.physical_fderiv_eLpNorm_two_le
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physical_fderiv_eLpNorm_two_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physical_eLpNorm_two_le_dissipation"
#check @MethbokeAddon.WeakFouriermanB.physical_eLpNorm_two_le_dissipation
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physical_eLpNorm_two_le_dissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physical_eLpNorm_two_le_dissipation"
#print axioms MethbokeAddon.WeakFouriermanB.physical_eLpNorm_two_le_dissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physical_eLpNorm_two_le_dissipation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.physical_laplacian_eLpNorm_two"
#check @MethbokeAddon.WeakFouriermanB.physical_laplacian_eLpNorm_two
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.physical_laplacian_eLpNorm_two"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.physical_laplacian_eLpNorm_two"
#print axioms MethbokeAddon.WeakFouriermanB.physical_laplacian_eLpNorm_two
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.physical_laplacian_eLpNorm_two"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.PHYSICAL_L6_FROM_DISSIPATION"
#check @MethbokeAddon.WeakFouriermanB.PHYSICAL_L6_FROM_DISSIPATION
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.PHYSICAL_L6_FROM_DISSIPATION"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.PHYSICAL_L6_FROM_DISSIPATION"
#print axioms MethbokeAddon.WeakFouriermanB.PHYSICAL_L6_FROM_DISSIPATION
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.PHYSICAL_L6_FROM_DISSIPATION"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.PHYSICAL_DERIVATIVE_L6_FROM_LAPLACIAN"
#check @MethbokeAddon.WeakFouriermanB.PHYSICAL_DERIVATIVE_L6_FROM_LAPLACIAN
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.PHYSICAL_DERIVATIVE_L6_FROM_LAPLACIAN"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.PHYSICAL_DERIVATIVE_L6_FROM_LAPLACIAN"
#print axioms MethbokeAddon.WeakFouriermanB.PHYSICAL_DERIVATIVE_L6_FROM_LAPLACIAN
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.PHYSICAL_DERIVATIVE_L6_FROM_LAPLACIAN"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_THREE_QUARTER_BOUND"
#check @MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_THREE_QUARTER_BOUND
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_THREE_QUARTER_BOUND"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_THREE_QUARTER_BOUND"
#print axioms MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_THREE_QUARTER_BOUND
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_THREE_QUARTER_BOUND"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_REAL_BOUND"
#check @MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_REAL_BOUND
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_REAL_BOUND"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_REAL_BOUND"
#print axioms MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_REAL_BOUND
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_REAL_BOUND"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_ABSORPTION"
#check @MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_ABSORPTION
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_ABSORPTION"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_ABSORPTION"
#print axioms MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_ABSORPTION
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_ABSORPTION"
