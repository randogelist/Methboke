# EHRENFEST-OBSTRUCTION

This supporting workstream develops the frozen **conditional** theorem

```text
ν > 0 → StoppedCommutatorBound ν → ¬ NSE_B ν.
```

It combines an exact Galerkin–Heisenberg representation with a stopped negative commutator rate for a bounded reciprocal-enstrophy observable. The initial datum is smooth and fixed across every cutoff. The proposed rate condition remains an explicit, unproved hypothesis.

The ten-step mathematical derivation is complete as a conditional argument. **Zero new Lean endpoints are implemented or accepted.** No global custom axiom is added. The existing WFB theorem and fixed repository goal retain their original finite-budget scope.

- [Cumulative B-tier derivation](../../EHRENFEST_OBSTRUCTION_B_TIER.txt)
- [Ten mid-tier checklist](CHECKLIST.md)
- [Probable 26-module Lean layout](LEAN_LAYOUT.md)
- [Machine module DAG](MODULE_PLAN.json) and [eight schematic interfaces](INTERFACES.lean.txt)
- [Operator/domain construction](OPERATOR_LAYOUT.txt) and [native package contract](NATIVE_PACKAGE_PLAN.json)
- [Machine endpoint ledger](obligations.json)
- [Readable source index](ANCHOR_INDEX.md)
- [47 exact pinned source records](ANCHOR_INDEX_v0_2.json)
- [Static package validation](VALIDATION.json)

The main new formal obligations are the unbounded generator/domain/core realization and the full-slab smooth-solution-to-Galerkin stability estimate. The mathematical proof of the latter uses an H2 residual estimate and first-exit bootstrap; it does not assume a uniform Galerkin budget.

Verification is external and cached only. No local Lean, Lake or kernel execution is permitted. This documentation package changes no proof, vendor, compiler, dependency lock or CI source and requests no compiler run.

Version 0.2 separates the coefficient-only conditional obstruction from its full Heisenberg interpretation. It records the same-datum canonical-family adapter, explicit real-time no-hit predicate, safe `T<S` front semantics, and a direct unitary-generator/resolvent route to self-adjointness. The ten milestones keep their full scope. No local or external compiler was run for this refinement.
