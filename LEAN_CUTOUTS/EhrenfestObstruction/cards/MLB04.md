# MLB04 — `SingularClosure.invariantGalerkinRhs_global_exists`

Actual forward global trajectory on the invariant real state for every initial state.

**Evidence:** `ACCEPTED_MODULE_SOURCE_REVIEWED_NO_NAMED_DECLARATION_AUDIT` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.GalerkinInvariant
```

[Raw cutout](../identities/MLB04.lean.txt) · [Full source context](../sources/S33_GalerkinInvariant.lean.txt) · [Pinned source, lines 205–211](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/GalerkinInvariant.lean#L205-L211)

```lean
theorem invariantGalerkinRhs_global_exists (ν : ℝ) (hν : 0 ≤ ν) (N : ℕ)
    (z₀ : InvariantGalerkinState N) :
    ∃ z : ℝ → InvariantGalerkinState N, z 0 = z₀ ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt z (invariantGalerkinRhs ν N (z t)) t := by
  exact forwardGlobalSolution_exists (invariantGalerkinRhs ν N)
    ((contDiff_invariantGalerkinRhs ν N).of_le (by norm_num))
    (invariantGalerkinRhs_dissipative ν hν N) z₀
```

## Context and reuse boundary

Quantifies t>=0 only. Backward completeness and global smooth dependence must be developed.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `eeaf7acef88635864a09fa92ca07745c19a62912`. Cutout SHA-256: `ea0a6c4e9045cde0ceacbc36a26591090abb4af53ae71a6b7e5c85696fe247f1`.
