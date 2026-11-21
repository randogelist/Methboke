import QFAH2Interpolation.Endpoint

set_option autoImplicit false
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

noncomputable section

open scoped BigOperators
open MethbokeAddon.QuasiFeffermanA

namespace QFAH2Interpolation.IndependentTypeChecks

-- Literal real L2 observables. No spectral-realization or interpolation
-- premise occurs in this independently stated signature.
example (u : PhysicalH2) :
    (∑ j : Fin 3, ‖physicalH2Gradient j u‖ ^ 2) ^ 2 ≤
      ‖physicalH2Velocity u‖ ^ 2 * ‖physicalH2Laplacian u‖ ^ 2 :=
  physicalH2_enstrophy_sq_le_energy_mul_laplacian u

-- Nontrivial constructor consumer: only the original concrete compact-test
-- weak derivative predicates are provided. The Laplacian is the literal
-- diagonal sum of the supplied L2 Hessian fields, without a norm assumption.
example (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (H : Fin 3 → Fin 3 → SpatialL2)
    (hG : SpatialWeakGradient v G) (hH : SpatialWeakHessian G H) :
    (∑ j : Fin 3, ‖G j‖ ^ 2) ^ 2 ≤
      ‖v‖ ^ 2 * ‖∑ j : Fin 3, H j j‖ ^ 2 := by
  have h := physicalH2_enstrophy_sq_le_energy_mul_laplacian
    (physicalH2OfWeakDerivatives v G H hG hH)
  simpa only [physicalH2OfWeakDerivatives_velocity,
    physicalH2OfWeakDerivatives_gradient, physicalH2Laplacian_apply,
    physicalH2OfWeakDerivatives_hessian] using h

-- Literal nine-entry Frobenius Hessian consumer. This retains constant one;
-- neither the number of coordinates nor the Hessian cardinality adds a factor.
example (u : PhysicalH2) :
    (∑ j : Fin 3, ‖physicalH2Gradient j u‖ ^ 2) ^ 2 ≤
      ‖physicalH2Velocity u‖ ^ 2 *
        (∑ j : Fin 3, ∑ k : Fin 3, ‖physicalH2Hessian j k u‖ ^ 2) := by
  rw [H2Spectral.physicalH2_hessian_norm_sq_eq_laplacian]
  exact physicalH2_enstrophy_sq_le_energy_mul_laplacian u

end QFAH2Interpolation.IndependentTypeChecks

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2_enstrophy_sq_le_energy_mul_laplacian"
#check @MethbokeAddon.QuasiFeffermanA.physicalH2_enstrophy_sq_le_energy_mul_laplacian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH2_enstrophy_sq_le_energy_mul_laplacian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH2_enstrophy_sq_le_energy_mul_laplacian"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH2_enstrophy_sq_le_energy_mul_laplacian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH2_enstrophy_sq_le_energy_mul_laplacian"
