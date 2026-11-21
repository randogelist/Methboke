import MethbokeAddon.QuasiFeffermanA.H2Spectral
import QFA.Assembly.AnalyticChain

/-!
# Actual whole-space H2 interpolation

The original physical H2 graph constructs its distributional derivative
witnesses. The accepted native spectral realization then supplies every
integrable Fourier moment used by the accepted quadratic-moment inequality.
Real complexification preserves each actual L2 norm exactly.

The endpoint has only an actual PhysicalH2 input. No spectral, interpolation,
Sobolev, solenoidal, or evolution premise is added. This is not sharp L6
Sobolev admission and does not supply the registered S6 constant.

Prepared outside the repository for matching authorized external verification.
No local Lean, Lake, or kernel execution has been performed.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace MethbokeAddon.QuasiFeffermanA

/-- The actual full-volume gradient, velocity and Laplacian obey the
constant-one interpolation inequality, including their zero-energy cases. -/
theorem physicalH2_enstrophy_sq_le_energy_mul_laplacian (u : PhysicalH2) :
    (∑ j : Fin 3, ‖physicalH2Gradient j u‖ ^ 2) ^ 2 ≤
      ‖physicalH2Velocity u‖ ^ 2 * ‖physicalH2Laplacian u‖ ^ 2 := by
  have hSpectral := nativeSpectralRealization_of_schwartzDerivativeWitnesses
    (physicalH2_schwartzDerivativeWitnesses u)
  have hInterpolation :=
    QFA.Assembly.AnalyticChain.interpolation_of_nativeSpectralRealization hSpectral
  simpa only [QFA.Endpoints.Agmon.gradientEnergy,
    QFA.Endpoints.Agmon.velocityEnergy, QFA.Endpoints.Agmon.laplacianEnergy,
    QFA.Endpoints.Representation.complexifyL2_norm] using hInterpolation

end MethbokeAddon.QuasiFeffermanA
