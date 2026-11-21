import R3EhrenfestDerivativeRepresentative.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform ContDiff BoundedContinuousFunction

namespace R3EhrenfestDerivativeRepresentative.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open MethbokeAddon.R3Ehrenfest.SharpCutoff
open MethbokeAddon.R3Ehrenfest.Bandlimited
open MethbokeAddon.R3Ehrenfest.SmoothRepresentative
open MethbokeAddon.R3Ehrenfest.DerivativeRepresentative

example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl

example (f : ComplexL2)
    (hf : Integrable (fun ξ : Space => f ξ) volume)
    (h1 : Integrable (fun ξ : Space => ‖ξ‖ * ‖f ξ‖) volume) (x e : Space) :
    fderiv ℝ (𝓕⁻ (fun ξ : Space => f ξ)) x e =
      (𝓕⁻ (fun ξ : Space =>
        ((2 * Real.pi * Complex.I) * (inner ℝ ξ e : ℂ)) • f ξ)) x :=
  fourierInv_integral_fderiv_apply f hf h1 x e

example (n : ℕ) (u : SpatialL2) (j : Fin 3) (x : Space) :
    fderiv ℝ (fun y : Space => sharpCutoffRepresentativeCLM n u y) x
      (EuclideanSpace.single j (1 : ℝ)) =
        sharpCutoffRepresentativeCLM n (cutoffDerivative n j u) x :=
  fderiv_sharpCutoffRepresentative_coordinate n u j x
example (n : ℕ) (u : SpatialL2) (j : Fin 3) (x : Space) :
    fderiv ℝ (fun y : Space => sharpCutoffRepresentativeCLM n u y) x
      (EuclideanSpace.single j (1 : ℝ)) =
        sharpCutoffRepresentativeCLM n (physicalH2Gradient j (sharpCutoffH2 n u)) x :=
  fderiv_sharpCutoffRepresentative_physicalH2Gradient n u j x

example (n : ℕ) (a : List (Fin 3)) : SpatialL2 →L[ℝ] SpatialL2 := cutoffWordCLM n a
example (n : ℕ) : cutoffWordCLM n [] = ContinuousLinearMap.id ℝ SpatialL2 := rfl
example (n : ℕ) (j : Fin 3) (a : List (Fin 3)) :
    cutoffWordCLM n (j :: a) = (cutoffDerivative n j).comp (cutoffWordCLM n a) := rfl
example (n : ℕ) (a : List (Fin 3)) (u : SpatialL2) :
    ‖cutoffWordCLM n a u‖ ≤ (cutoffDerivativeBound n) ^ a.length * ‖u‖ :=
  norm_cutoffWordCLM_apply_le n a u
example (v : Space → Space) : coordinateIterate [] v = v := rfl
example (j : Fin 3) (a : List (Fin 3)) (v : Space → Space) :
    coordinateIterate (j :: a) v =
      (fun x => fderiv ℝ (coordinateIterate a v) x (EuclideanSpace.single j (1 : ℝ))) := rfl
example (n : ℕ) (a : List (Fin 3)) (u : SpatialL2) (x : Space) :
    coordinateIterate a (fun y : Space => sharpCutoffRepresentativeCLM n u y) x =
      sharpCutoffRepresentativeCLM n (cutoffWordCLM n a u) x :=
  coordinateIterate_sharpCutoffRepresentative n a u x
example (n : ℕ) (a : List (Fin 3)) (u : SpatialL2) (x : Space) :
    ‖coordinateIterate a (fun y : Space => sharpCutoffRepresentativeCLM n u y) x‖ ≤
      bernsteinConstant n * (cutoffDerivativeBound n) ^ a.length * ‖u‖ :=
  coordinateIterate_sharpCutoffRepresentative_bound n a u x

end R3EhrenfestDerivativeRepresentative.ExpectedTypes

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fourierInv_integral_fderiv_apply"
#check @MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fourierInv_integral_fderiv_apply
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fourierInv_integral_fderiv_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fourierInv_integral_fderiv_apply"
#print axioms MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fourierInv_integral_fderiv_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fourierInv_integral_fderiv_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_coordinate"
#check @MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_coordinate
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_coordinate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_coordinate"
#print axioms MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_coordinate
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_coordinate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_physicalH2Gradient"
#check @MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_physicalH2Gradient
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_physicalH2Gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_physicalH2Gradient"
#print axioms MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_physicalH2Gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_physicalH2Gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.cutoffWordCLM"
#check @MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.cutoffWordCLM
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.cutoffWordCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.cutoffWordCLM"
#print axioms MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.cutoffWordCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.cutoffWordCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.norm_cutoffWordCLM_apply_le"
#check @MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.norm_cutoffWordCLM_apply_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.norm_cutoffWordCLM_apply_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.norm_cutoffWordCLM_apply_le"
#print axioms MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.norm_cutoffWordCLM_apply_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.norm_cutoffWordCLM_apply_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate"
#check @MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate"
#print axioms MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative"
#check @MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative"
#print axioms MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative_bound"
#check @MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative_bound
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative_bound"
#print axioms MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative_bound"
