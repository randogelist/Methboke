# Actual H2 heat dynamics in the physical L2 velocity space

**Status: prepared; matching cached external verification is pending.**

This package connects the actual H2 heat semigroup to the accepted
positive-time H1-to-H2 smoothing trajectory and strong L2 heat generator.
The datum is an actual `PhysicalH2` field. Its original velocity, gradient
and Hessian trace are retained by the H2 semigroup.

For positive viscosity and every positive elapsed time,

$$
\operatorname{heatTrajectory}_{\nu}(u\text{ viewed in }H^1,t)
=\operatorname{heatH2}_{\nu}(t)u.
$$

The proof compares the actual velocities and uses injectivity of the
physical H2 graph's velocity map. This equality is asserted only at
positive times. The arbitrary zero extension of the H1 smoothing
trajectory is never substituted for the original H2 datum.

Write $w(t)=\operatorname{heatH2}_{\nu}(\max(t,0))u$. For $\nu>0$ and $t>0$,
the derivative of its **SpatialL2 velocity** is

$$
\frac{d}{dt}V(w(t))=\nu\Delta w(t).
$$

The Laplacian path is continuous through time zero. For every finite
$T\ge0$, the exact Bochner integral equation is

$$
V(w(T))-V(u)=\int_0^T\nu\Delta w(t)\,dt.
$$

The equation is transferred from the accepted H1 generator equation by
agreement on the positive open integration interval. It includes $T=0$
and uses the original H2 velocity trace. Actual integrability of the
Laplacian density also follows from its proved continuity on finite
windows. No derivative, regularity or time-integrability witness is
supplied as an additional premise.

## Exact verification surface

The package has **four public theorems and six independent consumers**.
The namespace is `MethbokeAddon.QuasiFeffermanA.HeatH2Dynamics`.

| Public theorem | Exact scope |
|---|---|
| `heatTrajectory_eq_heatH2` | Actual H2 graph equality with the accepted smoothing trajectory, for positive viscosity and positive time. |
| `heatH2_laplacian_realTime_continuous` | Continuity of the actual Laplacian path through zero, for every nonnegative viscosity. |
| `heatH2_velocity_hasDerivAt` | Strong L2 velocity derivative equal to viscosity times the physical Laplacian of the same path, at positive time. |
| `heatH2_velocity_integrated_equation` | Exact physical L2 integral equation from the original H2 trace for every finite nonnegative horizon. |

The consumers expand the physical Laplacian into its three actual
diagonal Hessian entries, check genuine Bochner integrability, and
construct one common continuous H2 path carrying its original trace,
all positive-time L2 derivatives and all nonnegative-window equations.
Each public theorem requires a named exact-type report and a transitive
axiom audit permitting only `propext`, `Classical.choice` and `Quot.sound`.

## Scope boundary

This is a free-heat dynamics bridge for H2 initial data. It asserts no
H2-valued time derivative and no H2 initial trace for arbitrary H1 data.
The whole-real-line continuity statement uses the explicit nonnegative
clock; the evolution and derivative statements concern nonnegative and
positive physical times as specified above.

The inhomogeneous equation for regular forcing, forced energy estimate,
density passage to arbitrary time-L2 spatial-L2 forcing, maximal
regularity and nonlinear local theory remain separate constructions.
Step 3 and the general QFA/WFA roots remain open. Prepared source and
static review do not establish A-tier acceptance.

[Source](../MethbokeAddon/QuasiFeffermanA/HeatH2Dynamics.lean) ·
[Independent consumers](Audit.lean) ·
[Derivation](../../R3_NSE/QFA/DERIVATIONS/HEAT_H2_DYNAMICS_CHAIN.txt)

No local Lean, Lake or kernel audit is executed.
