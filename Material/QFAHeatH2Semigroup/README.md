# Actual physical H2 heat semigroup

**Status: prepared; matching cached external verification is pending.**

This package constructs the heat action on the actual complete physical
H2 graph for every nonnegative viscosity and elapsed time. It applies the
existing physical L2 heat semigroup to all thirteen graph fields: the
velocity, three weak gradients and nine ordered weak Hessian entries.
The accepted weak-gradient commutation theorem proves that the resulting
fields satisfy both levels of the native compact-test derivative relation.

The action is a bounded real linear map on `PhysicalH2`, contracts its
full inhomogeneous graph norm, and satisfies the semigroup law. Its initial
value is exactly the original H2 datum, and it is strongly continuous
through time zero:

\[
S^{(2)}_\nu(0)u=u,\qquad
\|S^{(2)}_\nu(t)u\|_{H^2}\le\|u\|_{H^2},\qquad
t\longmapsto S^{(2)}_\nu(t)u\text{ is continuous on }[0,\infty).
\]

Zero viscosity is included and gives the identity action. The coordinate
identities retain the literal actual velocity, gradient and Hessian. The
physical Laplacian and H2-to-H1 map commute with the action:

\[
\Delta S^{(2)}_\nu(t)u=S_\nu(t)\Delta u,\qquad
\iota_{2,1}S^{(2)}_\nu(t)u=S^{(1)}_\nu(t)\iota_{2,1}u.
\]

The proof of strong H2 continuity uses L2 continuity of each coordinate
and the exact finite sum defining the squared H2 norm. It needs no higher
derivative or supplied temporal regularity witness. The construction
imports the accepted `HeatSemigroup` and `PhysicalH2` sources; it does not
depend on the accepted L2 Duhamel or spatial-energy packages.

## Exact verification surface

The package has **15 public declarations: 13 theorems and two definitions**,
with **17 independent consumers**. The namespace is
`MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup`.

The definitions are the actual graph action `heatH2` and its bounded linear
map `heatH2CLM`. The theorems give literal velocity, gradient, Hessian,
Laplacian and H1 identities; addition and scalar multiplication; full H2
contraction; CLM evaluation; zero time; zero viscosity; the semigroup law;
and strong H2 continuity.

The independent audit also constructs one common H2 path carrying the
original initial trace, all thirteen coordinate identities, the Laplacian
identity and contraction at every nonnegative time. A further consumer
proves continuity of the actual Laplacian through its original H2-data
trace at zero.

Every public declaration requires a named exact-type report and a
transitive axiom audit permitting only `propext`, `Classical.choice` and
`Quot.sound`. Prepared source and static review do not establish A-tier
acceptance.

## Scope boundary

This supplies the original-trace H2 heat action needed for a subsequent
regular-forcing construction. The datum already belongs to the actual
physical H2 graph. H2 continuity at zero for arbitrary H1 data is outside
this scope.

The inhomogeneous heat equation for regular forcing, the forced
gradient/Laplacian energy estimate, the density passage to arbitrary
time-L2 spatial-L2 forcing, forced maximal regularity and nonlinear local
existence remain subsequent constructions. The general QFA and WFA roots
remain open.

[Source](../MethbokeAddon/QuasiFeffermanA/HeatH2Semigroup.lean) ·
[Independent consumers](Audit.lean) ·
[Derivation](../../R3_NSE/QFA/DERIVATIONS/HEAT_H2_SEMIGROUP_CHAIN.txt)

No local Lean, Lake or kernel audit is executed.
