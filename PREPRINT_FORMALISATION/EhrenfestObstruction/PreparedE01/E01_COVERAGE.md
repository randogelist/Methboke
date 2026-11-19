# Retained E01: candidate coverage

All entries below are prepared source. None is an external compilation or axiom-audit claim. The finalized scalar-root batch and repository files were not changed by this parallel work.

| Original E01 facet | Concrete candidate declarations | Boundary |
|---|---|---|
| Real finite-dimensional solenoidal phase | `GalerkinPhase`, `galerkinPhase_finiteDimensional`, `phaseCoeff_reality`, `phaseCoeff_solenoidal`, `phaseCoeff_meanZero` | Reuses native `InvariantGalerkinState`; no substitute phase record |
| Two-way coefficient identification | `phaseCoeff_injective`, `phaseFromCoeff_coeff`, `phaseFromCoeff_phaseCoeff`, `phaseCoeff_characterization` | Exactly the supported real-solenoidal coefficient families |
| Real orthonormal coordinates | `phaseCoordinates`, `phaseCoordinates_norm`, `phaseCoordinates_energy` | Actual real rank; no asserted dimension formula |
| Coordinate/volume adapter | `phaseVolume`, `phaseCoordinates_measurePreserving`, `phaseCoordinates_symm_measurePreserving`, `phaseVolume_map_linearIsometry` | Native phase-space Lebesgue volume, distinct from physical spatial volume |
| Physical synthesis semantics | `datumFourierCoeff_phaseSynthesis`, `phaseSynthesis_injective`, `phaseSynthesis_smoothSigmaZero`, `phaseSynthesis_integral_norm_sq`, `phaseSynthesis_gradient_energy` | Literal cube integration and finite Fourier sums |
| Actual Fourier-projected initial state | `phaseInitialState_coeff`, `phaseInitialState_synthesis`, `phaseInitialState_energy_le` | Later canonical-orbit lane must instantiate cutoff `n+1` and use ODE uniqueness |
| Actual smooth NSE field | `phaseRhs_coeff`, `phaseRhs_contDiff`, `phaseRhs_lipschitzOn_closedBall` | Native polynomial vector field; local Lipschitz constants depend on the finite cutoff and ball |
| Positive bounded self-adjoint Stokes | `phaseStokes_selfAdjoint`, `phaseStokes_poincare`, `phaseStokes_pos_of_ne_zero`, `phaseStokes_opNorm_le_lambdaMax`, `phaseStokes_synthesis` | Actual negative Laplacian; lower gap `4*pi^2`, upper bound `(2*pi)^2*N^2` from the native Euclidean cutoff |
| Orthogonal cutoff laws | `phaseCutoff_selfAdjoint`, `phaseCutoff_idempotent`, `phaseCutoff_orthogonal_residual`, `phaseCutoff_opNorm_le_one` | Concrete finite frequency mask inside the actual phase |
| Actual ambient Leray is orthogonal projection | `ambientLeray_eq_value`, `ambientLeray_apply`, `ambientLeray_range`, `ambientLeray_selfAdjoint`, `ambientLeray_idempotent` | Full ambient complex arrays regarded over the reals; only divergence is imposed here |
| Leray/real-phase compatibility | `phaseProjection_coe_eq_ambientLeray_of_reality`, `phaseRawTransport_reality`, `phaseTransport_coeff` | Reality is explicitly derived for the raw transport before using the projection identity |
| Projection/derivative commutation | `phaseDerivative_synthesis`, `phaseCutoff_derivative_commute`, `phaseCutoff_stokes_commute`, `ambientLeray_commutes_multiplier`, `ambientLeray_commutes_derivative`, `ambientLeray_commutes_cutoff` | Ambient scalar-multiplier commutation requires no real-input restriction |
| Actual nonsymmetric bilinear transport | `coefficientBilinearTransport`, `phaseTransportLinear`, `phaseTransport_coeff`, `phaseTransport_diagonal` | First argument advects the second; both real linearities and raw reality are proved |
| Polynomial structure and cancellation | `phaseRhs_eq_stokes_sub_transport`, `phaseTransport_diagonal_energy_zero`, `phaseRhs_radial_energy` | Quadratic structure is explicit linear-plus-bilinear decomposition; no separate Mathlib polynomial-object claim |
| Physical nonlinear pairing | `phaseSynthesis_convection_energy_zero`, `phaseTransport_diagonal_energy_eq_physical` | Literal cube integral; derived from native finite synthesis pairing, actual convection Fourier coefficients, and complex transport cancellation |

The frozen source collection covers the listed retained E01 interfaces at candidate level: 129 theorem candidates, 25 definitions, 3 abbreviations, 148 exact consumers, and 148 unexecuted axiom queries. Each of the 129 theorem candidates has an exact consumer and a named query. These are separate declarations; no single aggregate theorem named `REAL_SOLENOIDAL_GALERKIN_ALGEBRA` is asserted. No marker or externally accepted full-milestone status is issued here.

E02 remains separate: these candidates do not assert a jointly smooth complete two-sided flow, a group law, inverse Jacobians, or identification with the canonical family. They also do not assert any E03–E05 unitary-group or unbounded-generator conclusion. The finite-dimensional bounded Stokes operator is not the unbounded transport Hamiltonian.
