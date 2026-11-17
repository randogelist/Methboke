# SmallH12

`STATUS = EXTERNAL_PASS_AT_6440270` · `NO_LOCAL_LEAN`

Verified by [run 44052579373](https://github.com/randogelist/Methboke/actions/runs/44052579373)
at source `6440270ffe9b05b2956cd34c59c65f2fe341e8b8`, with a fresh exact-type
and standard-axiom audit. [Retained evidence](../../audits/material-6440270/summary.json)
keys acceptance to that source. The endpoint manifest retains its original
preparation status; it is not the current acceptance record.

Critical H1/2 small-data theorem; the explicit smallness hypothesis remains part of the exact theorem.

## Exact declarations

- [`SingularClosure.SMALL_DATA_CRITICAL_REGULARITY`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/SmallDataRoot.lean): nu>0; CriticalSigmaZero; criticalNonlinearConstant*norm(a)<nu.
- [`SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_REGULARITY`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/SmallDataRoot.lean): Same strict smallness; actual CriticalGlobalRegularity and CriticalDatumAX6.
- [`SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNIVERSAL_CONSTANT`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/SmallDataRoot.lean): Existence of a positive universal small-data constant; smallness retained.
- [`SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL.lean): Same strict smallness; one actual LH and positively smooth physical witness.

## Source closure

`Endpoint.lean` imports the exact upstream source modules. The complete transitive local source cutout is shared under `../_vendor`; the frozen mathlib source and object cache are supplied by the shared Lake project. No current upstream branch lookup is required at build time. This endpoint folder is a component of the complete `Material` project. The `ci/export_endpoint.py` tool constructs an independent Lake package containing this endpoint, its complete local dependency closure, its audit, the exact toolchain and the locked dependency manifest; no copy of the full Methlib repository is required.

`closure.json` records all 194 local dependency modules and their immutable source hashes. The endpoint manifest records the original repository, exact commit, source paths, declaration identities and assumptions.

## Compilation and audit

From `Material`, the shared build command builds this endpoint and its imported closure, then executes `lake env lean SmallH12/Audit.lean`. Lake traces and the registry dependency hashes retain passed unchanged modules and rebuild amended modules with their dependents.

`Audit.lean` emits exact declaration-type and axiom sentinels. Promotion requires a successful external compiler result and an axiom list contained in `[propext, Classical.choice, Quot.sound]`. Missing audit records, `sorryAx`, custom axioms and incomplete builds fail the gate.

The new finite-cap continuation theorem and universal analytic-germ admission statement are not asserted by this endpoint container.
