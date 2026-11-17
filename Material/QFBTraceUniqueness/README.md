# QFBTraceUniqueness

`STATUS = PENDING_EXTERNAL_CI` · `NO_LOCAL_LEAN`

Existing positive-time smooth reference and trace agreement required; no finite-cylinder localization is asserted.

## Exact declarations

- [`QuasiFeffermanB.positive_reference_strict_shift_serrin`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/Quasi-Fefferman-B/QuasiFeffermanB/TailUniqueness.lean): Global PositiveSmoothNSE reference and strictly positive shift required.
- [`QuasiFeffermanB.LH_UNIQUE_FUTURE_OF_SMOOTH_REFERENCE`](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/Quasi-Fefferman-B/QuasiFeffermanB/TailUniqueness.lean): Positive smooth reference plus actual weak-path agreement after a specified start required.

## Source closure

`Endpoint.lean` imports the exact upstream source modules. The complete transitive local source cutout is shared under `../_vendor`; the frozen mathlib source and object cache are supplied by the shared Lake project. No current upstream branch lookup is required at build time. This endpoint folder is a component of the complete `Material` project. The `ci/export_endpoint.py` tool constructs an independent Lake package containing this endpoint, its complete local dependency closure, its audit, the exact toolchain and the locked dependency manifest; no copy of the full Methlib repository is required.

`closure.json` records all 136 local dependency modules and their immutable source hashes. The endpoint manifest records the original repository, exact commit, source paths, declaration identities and assumptions.

## Compilation and audit

From `Material`, the shared build command builds this endpoint and its imported closure, then executes `lake env lean QFBTraceUniqueness/Audit.lean`. Lake traces and the registry dependency hashes retain passed unchanged modules and rebuild amended modules with their dependents.

`Audit.lean` emits exact declaration-type and axiom sentinels. Promotion requires a successful external compiler result and an axiom list contained in `[propext, Classical.choice, Quot.sound]`. Missing audit records, `sorryAx`, custom axioms and incomplete builds fail the gate.

The new finite-cap continuation theorem and universal analytic-germ admission statement are not asserted by this endpoint container.
