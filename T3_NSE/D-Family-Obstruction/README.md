# Periodic forced-NSE family obstruction

The local target is `Fefferman_D_Family_obstruction`: for every positive
viscosity and finite collection of distinct points of the unit three-torus,
construct a smooth prescribed force and a solution from rest that is smooth
before time one, has bounded preterminal cell energy, and is locally unbounded
at every prescribed point at time one. No global smooth periodic velocity and
pressure pair may solve the same datum and force.

This task starts the implementation of the previously indexed B-tier route.
The user has selected **Fefferman D** as the project goal. The family is its
construction route. The prior conditional `EHRENFEST_OBSTRUCTION` theorem and
its accepted evidence remain preserved foundations.

## First implementation layer

Native sources live in `Material/MethbokeAddon/FeffermanFamily/`:

| Module | Intended scope |
|---|---|
| `LocalBlowup.lean` | Local velocity blowup and its incompatibility with a continuous extension |
| `DisjointGerms.lean` | Finite disjoint carriers and local equality to a single summand |
| `FamilyContracts.lean` | Actual periodic forced-NSE fields, admissible force, competitor and finite-family contracts |

`Material/FeffermanFamilyFoundation/` registers the first package, with independent
exact consumer types and theorem-level axiom audits. [Run44655638162](https://github.com/randogelist/Methboke/actions/runs/44655638162)
verified 28 helper theorems and 11 contract declarations at 77a64245, using only
standard axioms. See the [A-tier helper register](FEFFERMAN_D_FOUNDATION_A_TIER.txt),
[evidence summary](../../audits/material-77a64245-family/summary.json) and
[implementation ledger](IMPLEMENTATION_STATUS.json) for exact scope.

## Current implementation step

The direct Fefferman-D endpoint is now prepared in an isolated source project:
`UpstreamSeed/Endpoint.lean` reuses the exact pinned upstream periodic theorem.
Its independent audit expands the initial-data, force-decay and global-solution
contracts. Matching external compiler/type/axiom verification is pending.
The existing Material project keeps Lean4.33.0; the isolated upstream proof uses
its own Lean4.34.0-rc2 and exact Mathlib lock. No objects cross that boundary.

The prescribed-site family remains a stronger, unfinished local target. Its
next native layer adds explicit growth-sequence selection, geometric blowup
transport, operator locality and exact finite disjoint-sum forced-NSE assembly.
These 22 helper theorems and 1 predicate are candidates pending the Material run.

## Route and remaining work

The [B-tier derivation](Fefferman_D_Family_obstruction_B_TIER.txt) gives the full
mathematical chain. The [shared source index](FEFFERMAN_C_D_FAMILY_OBSTRUCTION_INDEX.txt)
records the pinned source declarations and the boundaries of their use.

1. Fix classical smoothness, periodic pressure and the same-force competitor.
2. Import a compact smooth-force seed with initial rest.
3. Extract a local blowup point and recenter it.
4. Translate and delay compressed copies.
5. Pack finitely many copies at prescribed distinct torus sites.
6. Establish local equality of the finite sum to one copy or zero.
7. Transfer the exact nonlinear PDE and divergence through these local equalities.
8. Prove force admission and zero initial data.
9. Bound preterminal energy and transport growth to every site.
10. Lift viscosity before periodization and periodize inside a shifted cube.
11. Package the periodic candidate and exclude a smooth same-force competitor.
12. Assemble the quantified family statement and its one-site Fefferman-D projection.

The full root is not claimed by the foundation package. In particular it does
not assume the final family witness in place of constructing it. The compact
seed, placement, energy, periodization and same-force comparison adapters remain
separate obligations. The original energy-orthogonal response-force family is
not thereby admitted as a globally smooth-force example.

## Source and verification boundary

Methboke retains Lean `4.33.0` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. The literature reference is
`openai/NavierStokesAndEuler@f9e8bc5b38b6e212696e8a30e3e91517af887bbd`,
which uses Lean `4.34.0-rc2` and a different Mathlib pin. Its objects are not
imported into this package, and its theorem has not been ported or newly audited
here. No compiler or dependency pin is changed for the first layer.

Local Lean, Lake invoking Lean and local kernel audits are forbidden. The
existing external cached Material workflow passed 415 modules and 72 fresh
package audits (487 named type/axiom reports plus QFB). Matching evidence was
reviewed before accepting the helpers. This does not promote the unfinished root.
