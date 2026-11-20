# Spatial estimates, energy and continuation: source-cutout assessment

**Status:** source collection and static assessment only. No new Lean endpoint is
declared or accepted by this collection. No local Lean, Lake, kernel audit,
project runner or CI was executed.

**Source basis:** Methboke/AC-Integration at
ce7f809ad20b3498a63420a22d17b3c801dfd558.
The [catalog](catalog.json) records exact repositories, commits, original paths,
imports, inclusive source lines, namespaces, SHA256 hashes, evidence and the
remaining obligation for every excerpt. The governing endpoint order remains
the [twenty-step plan](../../A_TIER_PLAN.json).

## What the collection establishes

There are **16 exact contiguous cutouts and 13 byte-for-byte full original
modules**. Nine cutouts have existing named, scoped audit evidence; one has a
compiled-module receipt without a directly named audit root; two are pinned
Mathlib source references; four are newly attained upstream source references
under different pins. These are reference counts, not a percentage of the
NSE-A theorem completed.

The strongest additional finding is an **already accepted integral Grönwall
theorem** in ES03. It can consume the integral inequality derived from an
absolutely continuous physical enstrophy function. Consequently the proposed
route need not first build a new scalar AC Grönwall theorem. The actual
whole-space PDE-to-integral-inequality proof remains necessary.

The major unresolved endpoints here are the sharp physical Sobolev estimate,
actual strong energy/enstrophy evolution on initial closed slabs, and the
temporal small-product continuation argument. Available convection source
proofs reduce some spatial integration-by-parts work but do not provide
those PDE endpoints.

## Ranked remaining obligations

| Rank | Plan steps | Missing conclusion | Attained help and exact limit |
|---|---|---|---|
| 1 | P12–P13 | Actual R3 strong energy identity and absolute continuity of physical enstrophy on every [0,R], with 0 <= R < Tmax and the justified a.e. PDE inequality. | ES02 supplies scalar AC calculus; ES08 supplies a periodic physical model; ES14–ES15 supply upstream whole-space spatial convection proofs. None constructs the R3 trajectory or its temporal chain rule. |
| 2 | P09 | The physical Sobolev/interpolation and H2 norm identities, with the exact admissible constant S6^6 = 16/(27*pi^4). | ES01 supplies compact-C1 Sobolev with another explicit constant. ES13 supplies source-level MemSobolev 1 2 -> L6 membership. Neither proves the registered sharp homogeneous inequality. |
| 3 | P14–P15, P17 | A fixed positive small-product dissipation margin persists in time, bounds the same strong path, and yields genuine continuation/globality. | ES11 shows the same-front restart pattern in the periodic setting. ES12 is pointwise scalar absorption with a different historical coefficient. The R3 local H1 constructor and norm-controlled lifespan from P10–P11 remain prerequisites. |
| 4 | P12, P15–P16 | Instantiate proved scalar lemmas from actual finite strong-front data, retain the full endpoint budget, and exclude Tmax = tau_A. | ES03–ES06 directly support the assembly. The PDE facts cannot be supplied by an unconstructed global solution record. |

The first formal carrier/derivative adapter in the full plan lies earlier at
P01–P02 and is addressed by the spectral collection. Ranking the estimates here
does not change that dependency order.

## Exact reference inventory

Paths below are relative to this directory. Each .lean.txt file preserves the
original text; its corresponding complete module is under sources/.

| ID | Excerpt | Existing evidence | What to reuse |
|---|---|---|---|
| ES01 | [Compact-C1 Sobolev](cutouts/ES01_compact_c1_sobolev.lean.txt) | Pinned Mathlib source | Concrete inequality and constant; finite-dimensional domain, Haar measure, Hilbert codomain. |
| ES02 | [AC FTC and products](cutouts/ES02_absolutely_continuous_ftc.lean.txt) | Pinned Mathlib source | Scalar FTC, product identity and integration by parts on the entire closed interval. |
| ES03 | [Integral Grönwall](cutouts/ES03_integral_gronwall.lean.txt) | Named scoped audit | Variable continuous nonnegative coefficient; integrable product; no derivative premise on the controlled function. |
| ES04 | [Energy-envelope AC and identity](cutouts/ES04_energy_envelope_ac_identity.lean.txt) | Named scoped audits | Scalar primitive construction and exact residual-square identity. |
| ES05 | [Finite product budget](cutouts/ES05_finite_product_budget.lean.txt) | Named scoped audit | Finite-interval ED integrability and weighted energy bound. |
| ES06 | [Cutoff and strict selector](cutouts/ES06_registered_cutoff_and_selector.lean.txt) | Named scoped audits | Conditional numerical rewrite and an interior subcritical time. |
| ES07 | [Classical cubic square-budget estimate](cutouts/ES07_cubic_square_budget_classical.lean.txt) | Compiled module only | Exact-initial scalar estimate, retaining stronger continuity and pointwise derivative premises. |
| ES08 | [Periodic physical enstrophy](cutouts/ES08_periodic_physical_enstrophy.lean.txt) | Named scoped audits | Actual PDE derivative/cubic endpoint and initial-slab continuity pattern. |
| ES09 | [Full-budget uniform bound](cutouts/ES09_periodic_full_budget_bound.lean.txt) | Named scoped audit | One full improper budget bounds every shorter slab with the same constant. |
| ES10 | [Periodic H1 conversion](cutouts/ES10_periodic_h1_bound_poincare_boundary.lean.txt) | Named scoped audit | Exact location where periodic Poincare must be replaced in R3. |
| ES11 | [Same-front extension](cutouts/ES11_periodic_same_front_extension.lean.txt) | Named scoped audit | Restart before the endpoint, use a uniform lifespan, preserve old velocity and pressure. |
| ES12 | [Scalar absorption boundary](cutouts/ES12_scalar_absorption_scope.lean.txt) | Named scoped audits | Pointwise margin algebra; explicitly different threshold. |
| ES13 | [Upstream H1-to-L6 membership](cutouts/ES13_upstream_h1_l6_membership.lean.txt) | Source only, different pins | Schwartz approximation and Fatou extension to spectral/Bessel H1. |
| ES14 | [Upstream H1 convection integrability](cutouts/ES14_upstream_h1_convection_integrable.lean.txt) | Source only, different pins | L6-L2-L3 integrability with actual gradient representatives. |
| ES15 | [Upstream H1 IBP and cancellation](cutouts/ES15_upstream_h1_ibp_and_cancellation.lean.txt) | Source only, different pins | Weak Leibniz, divergence cancellation, L2-test extension and antisymmetry. |
| ES16 | [Upstream Schwartz trilinear bound](cutouts/ES16_upstream_schwartz_trilinear_sup_bound.lean.txt) | Source only, different pins | Component L2, gradient-L2 and L-infinity product bound. |

## A smaller scalar gap at P13–P15

The exact accepted declaration is
QFA.Endpoints.Comparison.CRITICAL_RELATIVE_ENERGY_GRONWALL. Its hypotheses are
coefficient continuity/nonnegativity, integrability of a*e, and

\[
e(t)\leq\delta+\int_0^t a(r)e(r)\,dr.
\]

It concludes

\[
e(t)\leq\delta\exp\!\left(\int_0^t a(r)\,dr\right).
\]

For the proposed strong path, the intended instantiation on [0,R] is

\[
e=Y=\|\nabla U\|_2^2,\qquad
a=\kappa Y^2,\qquad
\delta=Y(0),\qquad
\kappa=\pi^{-4}\nu^{-3}.
\]

Actual H1 continuity supplies continuity of Y, hence of a and a*Y on the
compact slab. After proving closed-slab absolute continuity and
Y' + nu*Z <= kappa*Y^3 almost everywhere, ES02 permits integration and removal
of the nonnegative dissipation term. That yields ES03's Volterra premise.
The full endpoint budget bounds every exponent by kappa*J_A.

The resulting intended uniform estimate is

\[
\|U(t)\|_{H^1}^{2}
\leq E_0+Y(0)\exp(\kappa J_A),
\]

using the separately derived energy bound E(t) <= E0. This is a proposed
instantiation of accepted scalar tools, not a newly checked theorem.
It avoids needing continuity of Z or of the enstrophy derivative at time zero.
The optional accumulated-dissipation version can instead control
e(t) = Y(t) + nu*integral_0^t Z after establishing its integral inequality.

ES07 remains useful as a complete classical scalar proof pattern. Its public
type explicitly asks for continuous y, z and d on [0,T], and a pointwise
derivative on (0,T). The rough-H1 route should not silently strengthen its
trajectory hypotheses to meet that interface or borrow smoothing from P19.

## Sharp constant and convection scope

The registered cutoff

\[
\tau_A=\frac{8\|a\|_2^4}{27\pi^4\nu^5}
\]

requires the spatial inequality with the specified admissible constant

\[
S_6=\frac{2^{2/3}}{\sqrt3\,\pi^{2/3}},
\qquad S_6^6=\frac{16}{27\pi^4}.
\]

ES06 proves a scalar rewrite **given** the sixth-power equality. It does not
prove Sobolev admissibility. ES01 has a different explicit constant; ES13's
public result is L6 membership. Its approximation machinery may help extend a
suitable quantitative inequality, but the conclusion alone does not supply
the homogeneous physical norm bound.

No sharp Talenti-admissibility proof was located in the inspected pinned
Mathlib/native estimate sources. This is a statement about these attained
modules and the search, not all possible Lean repositories. The existing
B-tier Talenti reference remains an analytic specification. This collection
does not change the registered cutoff to one using another constant.

ES14–ES15 provide substantial source-level lower work on the whole space:
H1 convection integrability and antisymmetry with actual weak-gradient
representatives. They can help discharge spatial cancellation in an energy
proof. The temporal PDE identity, pressure cancellation against the Laplacian,
H2/Fourier norm identifications and sharp nonlinear estimate remain separate.

The name convIntegralSchwartz_bound_H1 in ES16 must be read through its type.
Its last factor is a Schwartz sup seminorm, giving L-infinity control. It does
not prove an all-H1 trilinear inequality or the registered enstrophy estimate.
Likewise ES12 uses the historical threshold E*D < 4*pi^2*nu^4; this cannot
replace E*Y < nu^4/S6^6 in the new class proof.

## Finite-front, endpoint and same-path boundaries

ES04–ES06 have scalar finite-interval types. They apply after deriving the
energy data of a strong solution on a slab already known to exist.
The native LerayHopf.energy_product_budget_Ioo wrapper requires a global
Leray–Hopf record. That stronger wrapper is unnecessary for this route and
cannot supply an assumed global reference while globality is being proved.

ES09's budget covers the whole open endpoint interval. Separate finiteness
on every smaller closed slab does not supply the common bound needed for
continuation. P15 must cover both Tmax < tau_A and Tmax = tau_A, retain
extended budgets until finiteness is proved, and avoid assuming an endpoint
trace.

ES10 uses periodic Poincare explicitly. The R3 proof instead combines its
enstrophy bound with E(t) <= E0. ES11 provides the structural model: restart
strictly before an endpoint using a lifespan depending only on the H1 bound
and viscosity, prove overlap agreement, and obtain a longer version of the
same path. The R3 H1 constructor, uniqueness and maximality are not supplied
by this periodic theorem.

The zero datum is separate because the registered cutoff vanishes. The
positive-time selector requires nonzero M; no empty interval is used to
manufacture a restart. Universal finiteness of J_A remains open and is not
assumed by the conditional regularity-class equivalence.

## Provenance and evidence

The nine native named-audit cutouts match unchanged accepted source bytes at
afd67db40e71bd1412c82247a78598288deb611e, external run 44788963412.
Exact names, types, package identities and standard-axiom lists were read
from audits/material-afd67db4-qfa-accepted/evidence.zip, member current.json.
Every copied native module was compared byte-for-byte with both the current
source basis and that accepted commit. Acceptance applies only to the literal
types; periodic theorems remain periodic.

SingularClosure.CubicBudget has a PASS module receipt in the same retained
evidence, but its two selected cubic declarations are not directly named
audit roots there. The two Mathlib excerpts come from the exact native
dependency revision db584cd6d46c92f209a44c0f1c829460d327499d; no separate named
audit is asserted for them.

The four new upstream cutouts come from uda-lab/leray-hopf at
e704400f2fb2f26b2ee7f4372c3e1ecbbc82f3dc. Its source pins are Lean
v4.31.0-rc2 and Mathlib 15a89b2468bc01f1a6230d6e49ef5efc5286e502, differing
from the native project. Actual statement/proof bodies are present in the
selected blocks, but no matching native build, full transitive axiom audit
or carrier identification is claimed. Original modules contain historical
scaffold/status prose; their bytes are preserved and the catalog states
the present evidence boundary.

Full modules retain original imports and private helpers. This collection is
not a self-contained dependency closure and excerpts are not standalone
compilable files. Future integration must port required dependencies,
preserve actual theorem premises, and obtain matching external compilation,
exact-type consumers and named axiom audits before changing any endpoint's
acceptance status.
