# EHRENFEST-OBSTRUCTION

This supporting workstream develops the frozen **conditional** theorem

```text
ν > 0 → StoppedCommutatorBound ν → ¬ NSE_B ν.
```

It combines an exact Galerkin–Heisenberg representation with a stopped negative commutator rate for a bounded reciprocal-enstrophy observable. The initial datum is smooth and fixed across every cutoff. The proposed rate condition remains an explicit, unproved hypothesis.

The ten-step mathematical derivation is complete as a conditional argument. **The first six source modules and three package candidates are prepared; external acceptance is pending.** No global custom axiom is added. The existing WFB theorem and fixed repository goal retain their original finite-budget scope.

- [Cumulative B-tier derivation](../../EHRENFEST_OBSTRUCTION_B_TIER.txt)
- [Ten mid-tier checklist](CHECKLIST.md)
- [Source-exact identity cutouts](../../LEAN_CUTOUTS/EhrenfestObstruction/README.md) and [fast-route reading order](../../LEAN_CUTOUTS/EhrenfestObstruction/FAST_IDENTITIES.md)
- [Shortest identified Lean route: nine-module scalar root](FAST_ROUTE.md)
- [Five minimal interfaces](FAST_INTERFACES.lean.txt)
- [Full 31-module proposed layout](LEAN_LAYOUT.md)
- [Machine module DAG](MODULE_PLAN.json) and [eight schematic interfaces](INTERFACES.lean.txt)
- [Operator/domain construction](OPERATOR_LAYOUT.txt) and [native package contract](NATIVE_PACKAGE_PLAN.json)
- [Machine endpoint ledger](obligations.json)
- [Readable source index](ANCHOR_INDEX.md)
- [53 exact pinned source records](ANCHOR_INDEX_v0_3.json)
- [Static package validation](VALIDATION.json)

The main new formal obligations are the unbounded generator/domain/core realization and the full-slab smooth-solution-to-Galerkin stability estimate. The mathematical proof of the latter uses an H2 residual estimate and first-exit bootstrap; it does not assume a uniform Galerkin budget.

Verification is external and cached only. No local Lean, Lake or kernel execution is permitted. The implementation uses the unchanged compiler, dependency, vendor and CI configuration. The authorized push-main workflow supplies full cached compilation and fresh audits.

The v0.2 refinement separates the coefficient-only conditional obstruction from its full Heisenberg interpretation. It records the same-datum canonical-family adapter, explicit real-time no-hit predicate, safe `T<S` front semantics, and a direct unitary-generator/resolvent route to self-adjointness. The ten milestones keep their full scope. No local or external compiler was run for this refinement.

Version 0.3 shortens the root further: use one-cutoff mean-value contradiction and an eventual H1 enstrophy bound, supported by existing physical absorption and Fourier estimates. Hitting/escape and full H2 convergence remain separate stronger milestones. The root source closure excludes every operator module and the optional All bundle. This is a source-grounded proof-plan optimization, not a measured compiler-speed claim.

The initial identity-gathering stage is now available: 60 existing declarations/definitions, comprising the 53 indexed anchors and seven companion identities, with complete source/proof slices and 36 full pinned module snapshots. This is source extraction, not new implementation or formal acceptance. See the cutout catalog for original imports, contextual hypotheses and new adapters still required.

Current activation and exact package scopes: [IMPLEMENTATION_STATUS.json](IMPLEMENTATION_STATUS.json). E07 and helpers are candidates; the full root and full operator milestones remain open.
