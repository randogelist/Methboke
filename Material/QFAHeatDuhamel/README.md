# Actual finite-window L2 Duhamel response

**Status: prepared; matching cached external verification is pending.**

This package constructs the actual retarded Bochner integral

$$
K_\nu f(t)=\int_0^t S_\nu(t-s)f(s)\,ds
$$

using the native real `SpatialL2` heat semigroup, its physical elapsed-time
clock `(t - s).toNNReal`, and Lebesgue time measure. Forcing is an actual
function `f : ℝ → SpatialL2` with `MemLp 2` on `(0,T]`. Every nonnegative
viscosity and every finite nonnegative horizon are covered, including
zero viscosity and `T = 0`.

Joint strong continuity of the heat action proves the integrand's a.e.
strong measurability. Contraction and finite-window `MemLp 2` prove its
actual Bochner integrability. The response has zero initial trace, is
continuous on `[0,T]`, respects a.e. equality of forcing on the original
window, and has the proved addition and real scalar-multiplication laws.

For every `0 ≤ t ≤ T`, the exact estimates are

$$
\begin{aligned}
\|K_\nu f(t)\|_2
&\le \int_0^t\|f(s)\|_2\,ds\\
&\le \sqrt{t}\left(\int_0^t\|f(s)\|_2^2\,ds\right)^{1/2}\\
&\le \sqrt{T}\,\|f\|_{L^2((0,T);L^2)}.
\end{aligned}
$$

The final bound is also stated using the norm of the actual forcing class
`hf.toLp f`. Its constant is one, with no viscosity loss or spatial
spectral-gap assumption. Continuity follows from a fixed-window indicator
kernel and dominated convergence against the integrable forcing norm.

## Exact verification surface

The package has **15 public declarations: 14 theorems and one definition**.
Its **17 independent consumers** specify literal retarded integrals,
the actual forcing `Lp` norm, one common path carrying continuity, zero
trace, integral equality and the uniform bound, and the zero-viscosity
primitive. Every public declaration requires a named type report and a
transitive axiom audit permitting only `propext`, `Classical.choice` and
`Quot.sound`.

No measurability, integrability, continuity or constructed-response witness
is supplied as an extra input. The finite-window `MemLp 2` condition is
the forcing-space assumption from which these properties are derived.
Prepared source and static review do not establish A-tier acceptance.

## Scope boundary

This is the continuous L2 response and its low-frequency estimate.
Forced H1/H2 maximal regularity, the inhomogeneous derivative equation,
solenoidal response packaging and nonlinear local existence remain
subsequent constructions. The separate prepared
[QFAHeatDuhamelOperator package](../QFAHeatDuhamelOperator/README.md)
bundles this response as an actual continuous linear map from the forcing
`Lp` space to continuous physical L2 paths, with norm at most `sqrt T`,
zero initial trace and compatibility with original representatives.
Matching external verification of that five-declaration, seven-consumer
package is pending. This package retains its own 15-declaration,
17-consumer scope. The general QFA and WFA roots remain open.

[Source](../MethbokeAddon/QuasiFeffermanA/HeatDuhamel.lean) ·
[Independent consumers](Audit.lean) ·
[Derivation](../../R3_NSE/QFA/DERIVATIONS/HEAT_DUHAMEL_CHAIN.txt)

No local Lean, Lake or kernel audit is executed.
