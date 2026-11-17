# QFBCutoff

`STATUS = PENDING_EXTERNAL_CI` · `NO_LOCAL_LEAN`

Exact cutoff definitions and arithmetic; no additional PDE inference.

## Exact declarations

- [`QuasiFeffermanB.cutoff`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/Quasi-Fefferman-B/QuasiFeffermanB/Semantics.lean): norm(a)^4 / (8*pi^2*nu^5).
- [`QuasiFeffermanB.safeCutoff`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/Quasi-Fefferman-B/QuasiFeffermanB/Semantics.lean): 2*cutoff a nu.
- [`QuasiFeffermanB.CUTOFF_NONNEG`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/Quasi-Fefferman-B/QuasiFeffermanB/Cutoff.lean): Positive viscosity retained.
- [`QuasiFeffermanB.CUTOFF_ZERO`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/Quasi-Fefferman-B/QuasiFeffermanB/Cutoff.lean): Zero datum exact arithmetic.
- [`QuasiFeffermanB.CUTOFF_POS`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/Quasi-Fefferman-B/QuasiFeffermanB/Cutoff.lean): Nonzero datum and positive viscosity retained.
- [`QuasiFeffermanB.SAFE_CUTOFF_GT`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/Quasi-Fefferman-B/QuasiFeffermanB/Cutoff.lean): Nonzero datum and positive viscosity retained.

## Source closure

`Endpoint.lean` imports the exact upstream source modules. The complete transitive local source cutout is shared under `../_vendor`; the frozen mathlib source and object cache are supplied by the shared Lake project. No current upstream branch lookup is required at build time. This endpoint folder is a component of the complete `Material` project. The `ci/export_endpoint.py` tool constructs an independent Lake package containing this endpoint, its complete local dependency closure, its audit, the exact toolchain and the locked dependency manifest; no copy of the full Methlib repository is required.

`closure.json` records all 116 local dependency modules and their immutable source hashes. The endpoint manifest records the original repository, exact commit, source paths, declaration identities and assumptions.

## Compilation and audit

From `Material`, the shared build command builds this endpoint and its imported closure, then executes `lake env lean QFBCutoff/Audit.lean`. Lake traces and the registry dependency hashes retain passed unchanged modules and rebuild amended modules with their dependents.

`Audit.lean` emits exact declaration-type and axiom sentinels. Promotion requires a successful external compiler result and an axiom list contained in `[propext, Classical.choice, Quot.sound]`. Missing audit records, `sorryAx`, custom axioms and incomplete builds fail the gate.

The new finite-cap continuation theorem and universal analytic-germ admission statement are not asserted by this endpoint container.
