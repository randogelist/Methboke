# MLB02 — `SingularClosure.contDiff_invariantGalerkinRhs`

Smooth polynomial vector field restricted to the physical invariant state.

**Evidence:** `ACCEPTED_MODULE_SOURCE_REVIEWED_NO_NAMED_DECLARATION_AUDIT` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.GalerkinInvariant
```

[Raw cutout](../identities/MLB02.lean.txt) · [Full source context](../sources/S33_GalerkinInvariant.lean.txt) · [Pinned source, lines 156–160](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/GalerkinInvariant.lean#L156-L160)

```lean
theorem contDiff_invariantGalerkinRhs (ν : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (invariantGalerkinRhs ν N) := by
  exact (invariantGalerkinSubspace N).orthogonalProjectionOnto.contDiff.comp
    ((contDiff_hilbertGalerkinRhs ν N).comp
      (invariantGalerkinSubspace N).subtypeL.contDiff)
```

## Context and reuse boundary

No complete two-sided flow, derivative-of-flow or Jacobian conclusion.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `eeaf7acef88635864a09fa92ca07745c19a62912`. Cutout SHA-256: `62f43a95262a4ed68265c05163f988f9dcf0c807d2f62570fc9d3f650dcfe3e5`.
