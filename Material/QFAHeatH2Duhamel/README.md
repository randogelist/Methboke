# Actual H2 Duhamel response for continuous H2 forcing

**Status: prepared; matching cached external verification is pending.**

For ordinary continuous forcing `f : ℝ → PhysicalH2`, this package
constructs the actual retarded Bochner integral in the complete physical
H2 graph:

\[
U(t)=\int_0^t S^{(2)}_\nu(t-s)f(s)\,ds.
\]

The implementation uses the literal nonnegative elapsed-time clock
`(t - s).toNNReal` and every nonnegative viscosity. Joint strong H2
continuity proves the kernel is jointly continuous, hence genuinely
Bochner integrable on every finite interval. Native parametric interval
integration proves continuity of the H2-valued response, with exact
initial trace `U 0 = 0`.

All physical coordinate maps commute with the constructed integral.
In particular its velocity and Laplacian are exactly the existing L2
Duhamel integrals for the original coordinate forcing:

\[
V(U(t))=\int_0^t S_\nu(t-s)V(f(s))\,ds,\qquad
\Delta U(t)=\int_0^t S_\nu(t-s)\Delta f(s)\,ds.
\]

The same identities hold for each of the three actual gradients and nine
actual Hessian entries. The H2-to-H1 inclusion gives the literal integral
of the existing H1 heat action. For every `t ≥ 0`, full H2 contraction
also gives the forcing integral bound

\[
\|U(t)\|_{H^2}\le\int_0^t\|f(s)\|_{H^2}\,ds.
\]

## Exact verification surface

The package has **12 public declarations: 11 theorems and one definition**,
with **14 independent consumers**. The namespace is
`MethbokeAddon.QuasiFeffermanA.HeatH2Duhamel`.

The public constructor is `duhamelH2`. The theorems establish joint H2
heat continuity, joint kernel continuity, actual interval integrability,
zero trace, response continuity, the five velocity/gradient/Hessian/
Laplacian/H1 compatibility identities, and the full H2 integral bound.

The independent consumers use literal H2 and L2 retarded integrals and
the original forcing coordinates. They also assemble one common H2 path
carrying continuity, zero trace, integral equality, velocity and Laplacian
identities and the norm bound. A separate consumer shows that zero
viscosity gives the actual H2 primitive `∫ s in 0..t, f s`.

Every public declaration requires a named exact-type report and a
transitive axiom audit permitting only `propext`, `Classical.choice` and
`Quot.sound`. Prepared source and static review do not establish A-tier
acceptance.

## Scope boundary

The forcing assumption is exactly `Continuous f` with values in the
actual physical H2 graph. No response, integrability or temporal continuity
witness is supplied as an additional input.

The real-time definition extends the elapsed-time clock by `toNNReal`;
the proved continuity is global for that explicit extension. Its physical
retarded interpretation concerns nonnegative time. The original actual
spatial operators and Lebesgue time measure are retained.

The source depends on the separate H2 heat semigroup and the L2 Duhamel
constructor. It does not require the separate H2 free-dynamics bridge.
The forced differential equation, forced gradient/Laplacian energy
estimate, density passage to arbitrary time-L2 spatial-L2 forcing, maximal
regularity, solenoidal response and nonlinear local existence remain
subsequent constructions. The general QFA and WFA roots remain open.

[Source](../MethbokeAddon/QuasiFeffermanA/HeatH2Duhamel.lean) ·
[Independent consumers](Audit.lean) ·
[Derivation](../../R3_NSE/QFA/DERIVATIONS/HEAT_H2_DUHAMEL_CHAIN.txt)

No local Lean, Lake or kernel audit is executed.
