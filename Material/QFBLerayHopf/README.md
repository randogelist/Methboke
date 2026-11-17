# QFBLerayHopf

`STATUS = PENDING_EXTERNAL_CI` · `NO_LOCAL_LEAN`

Actual Leray-Hopf existence for physical L2 solenoidal mean-zero input and positive viscosity.

## Exact declarations

- [`QuasiFeffermanB.Q01_LERAY_HOPF_EXISTENCE`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/Quasi-Fefferman-B/QuasiFeffermanB/Endpoints/LerayHopfExistence.lean): nu>0 and EnergySigmaZero a; actual CriticalLerayHopf witness.

## Source closure

`Endpoint.lean` imports the exact upstream source modules. The complete transitive local source cutout is shared under `../_vendor`; the frozen mathlib source and object cache are supplied by the shared Lake project. No current upstream branch lookup is required at build time. This endpoint folder is a component of the complete `Material` project. The `ci/export_endpoint.py` tool constructs an independent Lake package containing this endpoint, its complete local dependency closure, its audit, the exact toolchain and the locked dependency manifest; no copy of the full Methlib repository is required.

`closure.json` records all 180 local dependency modules and their immutable source hashes. The endpoint manifest records the original repository, exact commit, source paths, declaration identities and assumptions.

## Compilation and audit

From `Material`, the shared build command builds this endpoint and its imported closure, then executes `lake env lean QFBLerayHopf/Audit.lean`. Lake traces and the registry dependency hashes retain passed unchanged modules and rebuild amended modules with their dependents.

`Audit.lean` emits exact declaration-type and axiom sentinels. Promotion requires a successful external compiler result and an axiom list contained in `[propext, Classical.choice, Quot.sound]`. Missing audit records, `sorryAx`, custom axioms and incomplete builds fail the gate.

The new finite-cap continuation theorem and universal analytic-germ admission statement are not asserted by this endpoint container.
