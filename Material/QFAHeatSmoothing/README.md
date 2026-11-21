# Actual positive-time heat smoothing into physical H2

**A-tier accepted at `ffbab0f5` / [run 44847013775](https://github.com/randogelist/Methboke/actions/runs/44847013775)** for the exact scoped declarations.
[Matching evidence](../../audits/material-ffbab0f5-qfa-accepted/independent-review.json). The general QFA root remains open.

For positive viscosity and time, this package constructs a continuous linear
map from the actual full-volume physical H1 graph into the actual H2 graph.
It constructs all nine real L2 Hessian fields by bounded real-even Fourier
multipliers and proves their compact-test weak derivative identities. The
velocity is exactly the existing heat semigroup, and the H1 inclusion is
exactly its established H1 action.

The native Laplacian has the literal multiplier
`-(2*pi)^2*norm(xi)^2*exp(-4*pi^2*nu*t*norm(xi)^2)` and satisfies
`norm(Delta heat u)^2 <= (nu*t)^(-1) * physicalH1Enstrophy u`.
The full H2 norm is at most `sqrt(1+(nu*t)^(-1)) * norm(u)`.
No H2 witness, smoothing estimate or new spectral identity is assumed.

All 26 named declarations passed independent exact consumers and fresh
named type/transitive-axiom audits. No local Lean was executed.

The time-integrated free/forced heat estimates, Duhamel construction and
nonlinear H1 local existence remain separate obligations. This package does
not close the general physical QFA root.

The mathematical chain is
`R3_NSE/QFA/DERIVATIONS/RESTART_HEAT_ZERO_CHAIN.txt`, section 3.
