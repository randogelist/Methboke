# Physical integration by parts and Laplacian energy

**Status: prepared; matching cached external verification is pending.**

This package derives the exact physical energy pairing

$$
\langle v,\Delta v\rangle_{L^2(\mathbb R^3)}
=-\sum_{j=1}^{3}\|\partial_jv\|_{L^2(\mathbb R^3)}^2
=-Y(v)
$$

for every actual `PhysicalH2` field. The velocity, three weak gradients,
weak Hessian and Laplacian are the existing physical graph operators on
full Lebesgue spatial volume. The enstrophy is the literal
`physicalH1Enstrophy (physicalH2ToH1 u)`, with no one-half normalization.

The stronger bilinear theorem pairs an arbitrary physical H1 field with
the Laplacian of an arbitrary physical H2 field:

$$
\langle u,\Delta v\rangle_{L^2}
=-\sum_{j=1}^{3}\langle\partial_j u,\partial_j v\rangle_{L^2}.
$$

The construction starts with the native compact-test weak derivatives.
Their proved Fourier symbols, complex Plancherel and the skew symmetry of
the imaginary first-derivative multiplier establish H1 integration by
parts. Applying it to each actual H2 gradient gives the bilinear identity.
Symmetry and the negative-enstrophy pairing follow. Native L2 inner-product
integrability justifies the actual integrals throughout.

## Exact verification surface

The package has **four public theorems and no public definitions**, with
**five independent consumers**. The namespace is
`MethbokeAddon.QuasiFeffermanA.HeatSpatialEnergy`.

| Public theorem | Exact scope |
|---|---|
| `physicalH1_gradient_integration_by_parts` | First-order integration by parts for two arbitrary actual H1 fields and each of the three coordinate directions. |
| `physicalH1H2_laplacian_pairing` | H1-H2 pairing with the literal sum of three gradient inner products. |
| `physicalH2_laplacian_symmetric` | Symmetric real L2 pairing of the actual Laplacian on the physical H2 graph. |
| `physicalH2_laplacian_enstrophy` | Exact diagonal pairing equal to negative actual H1 enstrophy. |

The consumers expand enstrophy into the three actual gradient squared
norms and retain the exact coefficient for an arbitrary real multiplier
`ν`: pairing with `ν • physicalH2Laplacian u` gives `-ν` times that sum.

Every public theorem requires a named exact-type report and a transitive
axiom audit permitting only `propext`, `Classical.choice` and `Quot.sound`.
No integration-by-parts, spectral pairing, boundary, derivative or
integrability witness is supplied as an additional hypothesis. Prepared
source and static review do not establish A-tier acceptance.

## Scope boundary

These are spatial energy identities. The symmetry theorem is an explicit
bilinear identity on the actual H2 graph; a theorem about the full domain
of an unbounded self-adjoint operator is outside this package.

The identities supply an ingredient for the subsequent forced heat energy
estimate. Forced H1/H2 maximal regularity, the inhomogeneous derivative
equation, solenoidal response packaging and nonlinear local existence
remain subsequent constructions. The general QFA and WFA roots remain
open.

[Source](../MethbokeAddon/QuasiFeffermanA/HeatSpatialEnergy.lean) ·
[Independent consumers](Audit.lean) ·
[Derivation](../../R3_NSE/QFA/DERIVATIONS/HEAT_SPATIAL_ENERGY_CHAIN.txt)

No local Lean, Lake or kernel audit is executed.
