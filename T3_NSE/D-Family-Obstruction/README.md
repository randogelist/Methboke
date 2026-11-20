# Periodic forced-NSE family obstruction

The project goal is **Fefferman D**. The stronger local target is
`Fefferman_D_Family_obstruction`: for every positive viscosity and finite
configuration of distinct unit-torus sites, construct a smooth prescribed
periodic force and a solution from rest that is smooth before time one, has
bounded preterminal cell energy, and blows up locally at every prescribed
site. The same force and datum must have no global smooth periodic velocity
and pressure competitor. **This family witness remains unproved.**

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

Remaining obligations are singular-seed admission; full transformed-PDE and
support laws; finite prescribed-site packing; smooth force and initial-data
admission; energy bounds; viscosity transport and generic-radius periodization;
same-force comparison; the family witness; and the literal family-to-D adapter.
The [B-tier derivation](Fefferman_D_Family_obstruction_B_TIER.txt) and
[source index](FEFFERMAN_C_D_FAMILY_OBSTRUCTION_INDEX.txt) retain that route.

## Separate direct-D verification

`UpstreamSeed/Endpoint.lean` prepares direct reuse of the pinned upstream
periodic theorem under its isolated Lean `4.34.0-rc2` environment. Its external
[run 44663007873](https://github.com/randogelist/Methboke/actions/runs/44663007873)
at `dd0e3550f7c662e3251d48194f4f70f3f6d9f628` remains pending in this record.
**Native assembly acceptance does not accept that direct-D endpoint.** Its
source-specific authority is `UpstreamSeed/CI_RUN_PLAN.json` and matching evidence.
The stronger prescribed-site family is separate from that direct route.

## Source and verification boundary

The native Material project retains Lean `4.33.0` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. The pinned upstream source is
`openai/NavierStokesAndEuler@f9e8bc5b38b6e212696e8a30e3e91517af887bbd`.
Its `4.34.0-rc2` objects are not imported into the native family package.

Verification used compatible caches: dependency EXACT and project PREFIX.
This is not an exact-cache benchmark. Local Lean, Lake invoking Lean and local
kernel audits remain forbidden; none was executed. The previous conditional
Ehrenfest and finite-budget WFB/QFB results retain their original premises.
