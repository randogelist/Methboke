# EHRENFEST-OBSTRUCTION

This supporting workstream develops the frozen **conditional** theorem

```text
ν > 0 → StoppedCommutatorBound ν → ¬ NSE_B ν.
```

It combines an exact Galerkin–Heisenberg representation with a stopped negative commutator rate for a bounded reciprocal-enstrophy observable. The initial datum is smooth and fixed across every cutoff. The proposed rate condition remains an explicit, unproved hypothesis.

The ten-step mathematical derivation is complete as a conditional argument. **Zero new Lean endpoints are implemented or accepted.** No global custom axiom is added. The existing WFB theorem and fixed repository goal retain their original finite-budget scope.

- [Cumulative B-tier derivation](../../EHRENFEST_OBSTRUCTION_B_TIER.txt)
- [Ten mid-tier checklist](CHECKLIST.md)
- [Machine endpoint ledger](obligations.json)
- [Readable source index](ANCHOR_INDEX.md)
- [35 exact pinned source records](ANCHOR_INDEX_v0_1.json)
- [Static package validation](VALIDATION.json)

The main new formal obligations are the unbounded generator/domain/core realization and the full-slab smooth-solution-to-Galerkin stability estimate. The mathematical proof of the latter uses an H2 residual estimate and first-exit bootstrap; it does not assume a uniform Galerkin budget.

Verification is external and cached only. No local Lean, Lake or kernel execution is permitted. This documentation package changes no proof, vendor, compiler, dependency lock or CI source and requests no compiler run.
