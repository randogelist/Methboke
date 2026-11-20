# Actual real L2 and physical H1 heat semigroup

This package constructs the heat operator on the actual full-volume real
vector L2 space and the native physical weak-gradient H1 graph. Its literal
Fourier symbol is

\[
e^{-4\pi^2\nu t\lVert\xi\rVert^2},\qquad \nu,t\in\mathbb R_{\ge0}.
\]

The implementation proves the actual Fourier action, real linearity, the
semigroup law, identity at zero time and zero viscosity, and L2 contraction.
Strong continuity follows from the exact squared-distance Fourier integral
and dominated convergence with the input's integrable Fourier energy density.
The H1 construction projects the supplied physical gradients, proves their
actual weak derivative relation, retains the velocity term in the norm, and
establishes H1 contraction and strong continuity at every nonnegative time.

The scoped B-tier chain is
`R3_NSE/A-Regularity-class/DERIVATIONS/REAL_HEAT_SEMIGROUP_CHAIN.txt`.
`Audit.lean` contains independently written complete expected types, literal
physical constructions and ordered named type/axiom reports for every public
declaration. All real nonnegative parameter notation is explicitly scoped.

**Status: prepared pending matching external verification.** The new shared
real-even multiplier dependency requires its own matching external evidence.
No local Lean, Lake, kernel or audit runner is executed. Only the standard
axioms `propext`, `Classical.choice` and `Quot.sound` are permitted.

This is the free linear heat edge of G01/P10. Actual H2 smoothing, forced-heat
maximal regularity, nonlinear local existence, uniqueness and continuation,
the canonical maximal solution and the finite-charge iff-global theorem
remain subsequent constructions. No conclusion from those layers is assumed
by this package or claimed from its preparation.
