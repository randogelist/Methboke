# Exact free-heat time-energy and actual L2-time H2 membership

Status: A-tier accepted at `000c1bd9`, [external run 44851575278](https://github.com/randogelist/Methboke/actions/runs/44851575278).
Exact scope: 19 named declarations (17 theorems, 2 definitions).
[Matching independent review](../../audits/material-000c1bd9-qfa-heat-time-accepted/independent-review.json); the complete run
passed 526 modules, 105 fresh package audits and 1,402 unique named reports,
plus fresh QFB, complete publication and final acceptance.

For arbitrary actual physical H1 input and positive viscosity, this package
constructs time integrability of the actual heat Laplacian and proves

    2 nu integral_0^T ||Delta S_nu(t)u||_2^2 dt = Y(u)-Y(S_nu(T)u).

The argument integrates the literal nonnegative Fourier density exactly,
proves product integrability using the original enstrophy density, and only
then applies Fubini. The singular pointwise 1/t estimate is never integrated
at zero. Together with the independently constructed measurable H2 trajectory
and physical H2 norm identity, it proves actual finite-window MemLp2 H2 and

    integral_0^T ||S_nu(t)u||_H2^2 dt <= T ||u||_H1^2 + Y(u)/(2 nu).

All finite T>=0 are included. The H2 trajectory is extended by zero at time
zero solely to obtain a total measurable function; no H2 initial trace is
asserted for arbitrary H1 input. The actual H1 heat trace remains u.

These are free heat results. The generator/primitive identity, forced heat,
nonlinear H1 existence and general QFA root remain separate obligations.
No local Lean, Lake or kernel audit is executed.
