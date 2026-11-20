# Periodic forced-NSE family obstruction

The project goal is **Fefferman D**. The stronger local target is
`Fefferman_D_Family_obstruction`: for every positive viscosity and finite
configuration of distinct unit-torus sites, construct a smooth prescribed
periodic force and a solution from rest that is smooth before time one, has
bounded preterminal cell energy, and blows up locally at every prescribed
site. The same force and datum must have no global smooth periodic velocity
and pressure competitor, without an additional global energy premise.
**The family is derived at B-tier from the pinned compact seed; its A-tier
formalization remains open.** The separate direct Fefferman-D endpoint is
already accepted at A-tier.

## Cumulative family derivation

The [B-tier derivation, version 1.6](Fefferman_D_Family_obstruction_B_TIER.txt)
periodizes each compressed seed inside the existing quarter-cube interface,
translates each periodic copy to its prescribed torus site, and sums copies
with disjoint closed carriers. Exact nonlinear cross terms vanish. Existing
same-force periodic comparison excludes a global competitor. This preferred
route needs no generic-radius packaging wrapper; the earlier common-cube
construction remains a documented alternative.

For any prescribed neighborhoods and `0 < tau < 1`, the witnesses can have
their spatial supports in those neighborhoods, force support in
`(1-tau, 1+tau)`, and initial rest through `1-tau`. One common compression
scale makes the sum of the velocity energy norm, viscosity-weighted
dissipation norm, and `L1_t L2_x` force norm arbitrarily small. It also meets
any finite list of positive mixed-norm force budgets with `3/p + 2/q > 3`.
The same sequence of times witnesses blowup at every prescribed site.

The zero-force specialization is obstructed: zero datum and identically zero
force imply zero velocity by the energy identity. For these spatially
localized witnesses, the projected force has positive squared time integral
on every terminal interval; removing it there would contradict positive-time
spatial analyticity and the fixed open region of zero velocity. No unforced
counterexample follows from the small-force limit.

[Cao, Chi and Nie, arXiv:2609.10262v4](https://arxiv.org/abs/2609.10262)
provide close direct precedents: Lemma 2.2 for seed energy/dissipation,
Proposition 3.3 for scaling, and Proposition 3.16 for simultaneous blowup in
finitely many disjoint regions. This derivation makes no novelty claim.

## Accepted native implementation

Native sources live in `Material/MethbokeAddon/FeffermanFamily/`.

| Module | Accepted scope |
|---|---|
| `LocalBlowup.lean` | Quantitative local blowup and continuous-extension obstruction |
| `DisjointGerms.lean` | Finite supported sums locally equal one active copy or zero |
| `FamilyContracts.lean` | Actual periodic forced-NSE contracts and scoped contract helpers |
| `GrowthSequence.lean` | Explicit growth-sequence selection and compact localization from the speed predicate |
| `CopyBlowup.lean` | Geometric recentering, translation and delayed parabolic blowup transport |
| `LocalDifferential.lean` | Locality of the native differential operators, including time zero |
| `DisjointNSE.lean` | Exact conditional finite disjoint-sum forced-NSE and divergence assembly |

The first package supplied 28 helper theorems and 11 contract declarations at
`77a64245`; see its [A-tier register](FEFFERMAN_D_FOUNDATION_A_TIER.txt).
The assembly package adds **22 helper theorems and 1 predicate**, accepted at
`f19531bca6816cea31c687629b9ab73ee6868169` by [run 44663707207](https://github.com/randogelist/Methboke/actions/runs/44663707207). The cumulative native family scope is
**50 helper theorems and 12 definitions/contracts**.

The accepted run covered 420 modules (415 reused, 5 fresh), 73 fresh package
audits, 510 named type/axiom reports plus a fresh QFB cutout, and 183 external
controls. All reports used only `propext`, `Classical.choice` and `Quot.sound`.
Independent matching source/type/axiom review passed 4,995 checks; publication
and final acceptance passed. See the [assembly A-tier register](FEFFERMAN_D_ASSEMBLY_A_TIER.txt),
[evidence summary](../../audits/material-f19531bc-assembly/summary.json) and
[implementation ledger](IMPLEMENTATION_STATUS.json).

## Exact closure boundary

The accepted additions establish sequence selection from an explicit speed
hypothesis, geometric transport of an existing blowup point, operator locality,
and conditional PDE assembly from supplied copy equations and fixed disjoint
carriers. They do not construct the singular seed or the actual placed copies.

Remaining formal obligations are singular-seed admission; full transformed-PDE
and support laws; finite prescribed-site packing; per-copy periodization and
torus translation; smooth force and initial-data admission; quantitative norm
bounds; same-force comparison; the family witness; and its literal family-to-D
adapter. The next scoped endpoint is admission of the same compact seed and
the full delayed-copy contract. The
[source index](FEFFERMAN_C_D_FAMILY_OBSTRUCTION_INDEX.txt) distinguishes these
open formal adapters from the closed B-tier chain.

## Separate direct-D verification

`UpstreamSeed/Endpoint.lean` explicitly reuses the pinned upstream periodic
theorem under its isolated Lean `4.34.0-rc2` environment. The direct endpoint
`Methboke.FeffermanD.Fefferman_D` is **accepted at A-tier** at
`66a529248d3198ed70dc5489d82868bc33a37796` by
[run 44768857811](https://github.com/randogelist/Methboke/actions/runs/44768857811):
605 modules, literal contract/type checks and five fresh named axiom reports
(three predicates and two theorems) passed, using only
`propext`, `Classical.choice` and `Quot.sound`. Evidence retention, cache
publication and final acceptance passed. See
[the acceptance receipt](UpstreamSeed/ACCEPTANCE.json) and
[retained artifact 14649221097](https://github.com/randogelist/Methboke/actions/runs/44768857811/artifacts/14649221097).

The earlier [run 44663007873](https://github.com/randogelist/Methboke/actions/runs/44663007873)
at `dd0e3550f7c662e3251d48194f4f70f3f6d9f628` passed verification but failed
evidence retention; the accepted rerun supersedes that obstruction.
Direct-D acceptance does not certify the stronger prescribed-site family.
The bare existential D theorem does not imply its compact seed or family;
the B-tier derivation explicitly uses the stronger upstream compact-seed theorem.

## Source and verification boundary

The native Material project retains Lean `4.33.0` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. The pinned upstream source is
`openai/NavierStokesAndEuler@f9e8bc5b38b6e212696e8a30e3e91517af887bbd`.
Its `4.34.0-rc2` objects are not imported into the native family package.

Verification used compatible caches: dependency EXACT and project PREFIX.
This is not an exact-cache benchmark. Local Lean, Lake invoking Lean and local
kernel audits remain forbidden; none was executed. The previous conditional
Ehrenfest and finite-budget WFB/QFB results retain their original premises.
