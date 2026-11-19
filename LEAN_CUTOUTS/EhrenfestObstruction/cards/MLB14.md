# MLB14 — `SingularClosure.SOBOLEV_DIVERGENCE_PRODUCT_NORM_BOUND`

Useful explicit bilinear Sobolev product bound for Fourier comparison estimates.

**Evidence:** `ACCEPTED_MODULE_SOURCE_REVIEWED_NO_NAMED_DECLARATION_AUDIT` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.FourierSobolevProduct
```

[Raw cutout](../identities/MLB14.lean.txt) · [Full source context](../sources/S30_FourierSobolevProduct.lean.txt) · [Pinned source, lines 199–205](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/FourierSobolevProduct.lean#L199-L205)

```lean
theorem SOBOLEV_DIVERGENCE_PRODUCT_NORM_BOUND (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c d : TorusSobolev (r + 2),
      ‖sobolevDivergenceProduct r c d‖ ≤ C * ‖c‖ * ‖d‖ := by
  obtain ⟨C, hC, hbound⟩ := SOBOLEV_DIVERGENCE_PRODUCT_MEM_NORM_BOUND r
  refine ⟨C, hC, ?_⟩
  intro c d
  exact (hbound c d).choose_spec
```

## Context and reuse boundary

Loses two derivatives in this formulation; does not by itself establish the needed H2 stability/bootstrap inequality.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `0648e014e3ae54a267b9a2bd32b485d280adc0bb`. Cutout SHA-256: `b15d5f04429307393dbe3b4638aebb91bff9722998599fbc403a18deb4878450`.
