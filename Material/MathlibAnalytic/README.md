# MathlibAnalytic

`STATUS = PENDING_EXTERNAL_CI` · `NO_LOCAL_LEAN`

Convergent analytic-germ semantics, restriction, identity and smoothness on already-existing domains; no NSE continuation assertion.

## Exact declarations

- [`AnalyticAt`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Analytic/Basic.lean): Existence of a convergent formal multilinear power series at the specified point.
- [`AnalyticOnNhd`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Analytic/Basic.lean): AnalyticAt at every point of the specified set.
- [`AnalyticOnNhd.mono`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Analytic/Basic.lean): Restriction to a subset; no domain extension.
- [`HasFPowerSeriesOnBall.uniform_geometric_approx`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Analytic/Basic.lean): Actual convergent series and strict subradius required.
- [`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Analytic/Uniqueness.lean): Both analytic representatives and neighborhood equality required.
- [`AnalyticOnNhd.contDiffOn_of_completeSpace`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/ContDiff/Defs.lean): Complete target space; conversion on an already-existing analytic domain.
- [`contDiffOn_of_locally_contDiffOn`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/ContDiff/Defs.lean): One function already defined; local smoothness hypotheses required.

## Source closure

`Endpoint.lean` imports the exact upstream source modules. The complete transitive local source cutout is shared under `../_vendor`; the frozen mathlib source and object cache are supplied by the shared Lake project. No current upstream branch lookup is required at build time. This endpoint folder is a component of the complete `Material` project. The `ci/export_endpoint.py` tool constructs an independent Lake package containing this endpoint, its complete local dependency closure, its audit, the exact toolchain and the locked dependency manifest; no copy of the full Methlib repository is required.

`closure.json` records all 0 local dependency modules and their immutable source hashes. The endpoint manifest records the original repository, exact commit, source paths, declaration identities and assumptions.

## Compilation and audit

From `Material`, the shared build command builds this endpoint and its imported closure, then executes `lake env lean MathlibAnalytic/Audit.lean`. Lake traces and the registry dependency hashes retain passed unchanged modules and rebuild amended modules with their dependents.

`Audit.lean` emits exact declaration-type and axiom sentinels. Promotion requires a successful external compiler result and an axiom list contained in `[propext, Classical.choice, Quot.sound]`. Missing audit records, `sorryAx`, custom axioms and incomplete builds fail the gate.

The new finite-cap continuation theorem and universal analytic-germ admission statement are not asserted by this endpoint container.
