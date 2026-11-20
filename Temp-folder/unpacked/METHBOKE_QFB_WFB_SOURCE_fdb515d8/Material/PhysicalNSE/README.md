# PhysicalNSE

`STATUS = EXTERNAL_PASS_AT_6440270` · `NO_LOCAL_LEAN`

Verified by [run 44052579373](https://github.com/randogelist/Methboke/actions/runs/44052579373)
at source `6440270ffe9b05b2956cd34c59c65f2fe341e8b8`, with a fresh exact-type
and standard-axiom audit. [Retained evidence](../../audits/material-6440270/summary.json)
keys acceptance to that source. The endpoint manifest retains its original
preparation status; it is not the current acceptance record.

Actual positive-time smooth PDE realization from an existing all-order Sobolev flow structure; no arbitrary-data existence or analytic upgrade is asserted.

## Exact declarations

- [`SingularClosure.CriticalPositiveSobolevFlow.velocity_spacetime_smooth`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalPositiveFlow.lean): Existing compatible CriticalPositiveSobolevFlow required.
- [`SingularClosure.CriticalPositiveSobolevFlow.pressure_spacetime_smooth`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalPositiveFlow.lean): Existing compatible CriticalPositiveSobolevFlow required.
- [`SingularClosure.CRITICAL_POSITIVE_PHYSICAL_NSE`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalPositiveFlow.lean): Existing compatible flow realizes actual positively smooth physical NSE.

## Source closure

`Endpoint.lean` imports the exact upstream source modules. The complete transitive local source cutout is shared under `../_vendor`; the frozen mathlib source and object cache are supplied by the shared Lake project. No current upstream branch lookup is required at build time. This endpoint folder is a component of the complete `Material` project. The `ci/export_endpoint.py` tool constructs an independent Lake package containing this endpoint, its complete local dependency closure, its audit, the exact toolchain and the locked dependency manifest; no copy of the full Methlib repository is required.

`closure.json` records all 96 local dependency modules and their immutable source hashes. The endpoint manifest records the original repository, exact commit, source paths, declaration identities and assumptions.

## Compilation and audit

From `Material`, the shared build command builds this endpoint and its imported closure, then executes `lake env lean PhysicalNSE/Audit.lean`. Lake traces and the registry dependency hashes retain passed unchanged modules and rebuild amended modules with their dependents.

`Audit.lean` emits exact declaration-type and axiom sentinels. Promotion requires a successful external compiler result and an axiom list contained in `[propext, Classical.choice, Quot.sound]`. Missing audit records, `sorryAx`, custom axioms and incomplete builds fail the gate.

The new finite-cap continuation theorem and universal analytic-germ admission statement are not asserted by this endpoint container.
